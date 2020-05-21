#!/usr/bin/env python3

from __future__ import annotations

import argparse
import difflib
import json
import os
import posixpath
import re
import shutil
import sys
import time
import urllib.parse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Optional

__version__ = "0.1.0"

CACHE_FILE = ".mdresurrectlink_cache.json"
BAK_SUFFIX = ".mdresurrectlink.bak"

RE_FENCE = re.compile(r"^\s*(`{3,}|~{3,})")
RE_INLINE_CODE = re.compile(r"`[^`\n]*`")
RE_HEADING = re.compile(r"^(#{1,6})[ \t]+(.*?)[ \t]*#*[ \t]*$", re.MULTILINE)
RE_SETEXT = re.compile(r"^(?!#)[^\n]+?[ \t]*\n(?:=+|-+)[ \t]*$", re.MULTILINE)
RE_HTML_ANCHOR = re.compile(
    r"<a\b[^>]*?(?:name|id)=[\"']([^\"']+)[\"']", re.IGNORECASE)
RE_INLINE_LINK = re.compile(r"(!?)\[([^\]]*)\]\(\s*<?([^>\s)]+)>?(?:\s+[^)]*)?\)")
RE_REF_DEF = re.compile(
    r"^[ \t]{0,3}\[([^\]]+)\]:[ \t]*<?([^>\s]+)>?", re.MULTILINE)
RE_REF_FULL = re.compile(r"(!?)\[([^\]]+)\]\[([^\]]*)\]")
RE_REF_SHORT = re.compile(r"(!?)\[([^\]]+)\](?![\[(:])")

EXTERNAL_SCHEMES = (
    "http://", "https://", "ftp://", "mailto:", "tel:",
    "data:", "javascript:", "irc://", "xmpp:",
)

DEFAULT_EXCLUDED_DIRS = {".git", ".hg", ".svn", ".obsidian", ".trash", "node_modules"}


@dataclass
class LinkRef:
    file: Path
    line: int
    col: int
    start: int
    end: int
    target: str
    text: str
    is_image: bool
    kind: str


@dataclass
class Issue:
    file: str
    line: int
    col: int
    level: str
    category: str
    target: str
    detail: str
    suggestion: str = ""


@dataclass
class Stats:
    files_scanned: int = 0
    links_checked: int = 0
    anchors_checked: int = 0
    broken: int = 0
    fixed: int = 0
    would_fix: int = 0
    elapsed: float = 0.0


def github_slug(title: str, used: set) -> str:
    s = title.strip().lower()
    s = re.sub(r"[^\w\s-]", "", s, flags=re.UNICODE)
    s = re.sub(r"\s+", "-", s)
    base, n = s, 0
    while s in used:
        n += 1
        s = f"{base}-{n}"
    used.add(s)
    return s


def mask_code(text: str) -> str:
    lines = text.splitlines(keepends=True)
    masked, in_fence, fence_ch = [], False, ""
    for ln in lines:
        m = RE_FENCE.match(ln)
        if m:
            ch = m.group(1)[0]
            if not in_fence:
                in_fence, fence_ch = True, ch
            elif ch == fence_ch:
                in_fence = False
            masked.append(re.sub(r"[^\r\n]", " ", ln))
            continue
        masked.append(re.sub(r"[^\r\n]", " ", ln) if in_fence else ln)
    cleaned = "".join(masked)
    return RE_INLINE_CODE.sub(lambda m: " " * len(m.group(0)), cleaned)


def extract_headings(text: str) -> list:
    cleaned = mask_code(text)
    used: set = set()
    slugs = [github_slug(m.group(2), used) for m in RE_HEADING.finditer(cleaned)
             if m.group(2).strip()]
    for m in RE_SETEXT.finditer(cleaned):
        title = m.group(0).splitlines()[0].strip()
        if title and not RE_FENCE.match(title):
            slugs.append(github_slug(title, used))
    slugs += [m.group(1) for m in RE_HTML_ANCHOR.finditer(cleaned)]
    return slugs


def _line_col(text: str, offset: int) -> tuple:
    return text.count("\n", 0, offset) + 1, offset - text.rfind("\n", 0, offset)


def extract_links(path: Path, text: str) -> tuple:
    cleaned = mask_code(text)
    links = []
    ref_defs = {m.group(1).strip().lower(): m.group(2)
                for m in RE_REF_DEF.finditer(cleaned)}

    def add(m, is_img, kind, target, txt):
        line, col = _line_col(cleaned, m.start())
        links.append(LinkRef(path, line, col, m.start(), m.end(), target,
                             txt, is_img, kind))

    for m in RE_INLINE_LINK.finditer(cleaned):
        add(m, bool(m.group(1)), "inline", m.group(3), m.group(2))
    for m in RE_REF_FULL.finditer(cleaned):
        label = m.group(3).strip().lower() or m.group(2).strip().lower()
        if label in ref_defs:
            add(m, bool(m.group(1)), "ref-full", ref_defs[label], m.group(2))
    for m in RE_REF_SHORT.finditer(cleaned):
        label = m.group(2).strip().lower()
        if label in ref_defs:
            add(m, bool(m.group(1)), "ref-short", ref_defs[label], m.group(2))
    return links, ref_defs


def split_target(target: str) -> tuple:
    if "#" in target:
        p, frag = target.split("#", 1)
        return p, frag
    return target, ""


class VaultIndex:

    def __init__(self, root: Path, files: list, disk_cache: Optional[dict] = None):
        self.root = root
        self.files = files
        self._anchors_mem: dict = {}
        self._disk_cache = disk_cache or {}
        self._by_lower: dict = {}
        self._by_name: dict = {}
        for p in files:
            rel = p.relative_to(root).as_posix().lower()
            self._by_lower[rel] = p
            self._by_name.setdefault(p.name.lower(), []).append(p)

    def headings_for(self, path: Path) -> list:
        key = str(path)
        try:
            mtime = path.stat().st_mtime
        except OSError:
            return []
        ck = (key, mtime)
        if ck in self._anchors_mem:
            return self._anchors_mem[ck]
        rel = path.relative_to(self.root).as_posix()
        hit = self._disk_cache.get(rel)
        if hit and hit.get("mtime") == mtime:
            slugs = hit["headings"]
        else:
            try:
                slugs = extract_headings(path.read_text(encoding="utf-8"))
            except (OSError, UnicodeDecodeError):
                slugs = []
            self._disk_cache[rel] = {"mtime": mtime, "headings": slugs}
        self._anchors_mem[ck] = slugs
        return slugs

    def dump_cache(self) -> dict:
        return self._disk_cache

    @staticmethod
    def _norm(p: Path) -> Path:
        return Path(os.path.normpath(str(p)))

    def target_to_candidate(self, current: Path, target: str) -> Optional[Path]:
        t = urllib.parse.unquote(target).strip()
        if not t or t.startswith(EXTERNAL_SCHEMES) or t.startswith("//"):
            return None
        path_part, _ = split_target(t)
        if not path_part:
            return current
        if path_part.startswith("/"):
            return self._norm(self.root / path_part.lstrip("/"))
        return self._norm(current.parent / path_part)

    def exists_in_vault(self, cand: Path) -> bool:
        try:
            cand.relative_to(self.root)
        except ValueError:
            return False
        return cand.exists()

    def lookup_case_insensitive(self, current: Path, target: str) -> Optional[Path]:
        t = urllib.parse.unquote(split_target(target)[0]).lstrip("/")
        rel = posixpath.normpath(t).lower()
        return self._by_lower.get(rel)

    def lookup_unique_basename(self, target: str) -> Optional[Path]:
        name = posixpath.basename(urllib.parse.unquote(split_target(target)[0]))
        hits = self._by_name.get(name.lower(), [])
        return hits[0] if len(hits) == 1 else None

    def lookup_fuzzy(self, current: Path, target: str, cutoff: float = 0.82) -> Optional[Path]:
        t = posixpath.normpath(urllib.parse.unquote(split_target(target)[0]).lstrip("/")).lower()
        if not t:
            return None
        guess = difflib.get_close_matches(t, self._by_lower.keys(), n=1, cutoff=cutoff)
        return self._by_lower[guess[0]] if guess else None

    def relpath_from(self, current: Path, dest: Path) -> str:
        rel = os.path.relpath(dest, current.parent).replace(os.sep, "/")
        return rel


def check_file(path: Path, index: VaultIndex) -> tuple:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as exc:
        rel = path.relative_to(index.root).as_posix()
        return [], [Issue(rel, 0, 0, "error", "missing-file", str(path),
                          f"无法读取文件: {exc}")]
    links, _ = extract_links(path, text)
    rel = path.relative_to(index.root).as_posix()
    issues = []
    for lk in links:
        cand = index.target_to_candidate(path, lk.target)
        if cand is None:
            continue
        path_part, frag = split_target(urllib.parse.unquote(lk.target))
        frag = urllib.parse.unquote(frag)

        if not index.exists_in_vault(cand):
            cat = "missing-image" if lk.is_image else "missing-file"
            issues.append(Issue(rel, lk.line, lk.col, "error", cat, lk.target,
                                "目标不存在" + ("（图片）" if lk.is_image else "")))
            continue

        if frag:
            anchor_file = path if cand == path else cand
            if anchor_file.suffix.lower() in (".md", ".markdown", ".mdown"):
                slugs = index.headings_for(anchor_file)
                if slugs and frag not in slugs:
                    cat = ("missing-same-anchor" if cand == path
                           else "missing-anchor")
                    issues.append(Issue(rel, lk.line, lk.col, "warn", cat,
                                        lk.target, f"锚点 '{frag}' 不在标题中",
                                        _anchor_hint(frag, slugs)))
    return links, issues


def _anchor_hint(frag: str, slugs: list) -> str:
    guess = difflib.get_close_matches(frag, slugs, n=1, cutoff=0.6)
    return f"你是不是想写: #{guess[0]}" if guess else ""


@dataclass
class Fix:
    link: LinkRef
    new_target: str
    strategy: str


def suggest_fix(lk: LinkRef, index: VaultIndex, allow_fuzzy: bool = False) -> Optional[Fix]:
    cur, root = lk.file, index.root
    raw_path, frag = split_target(lk.target)
    frag = urllib.parse.unquote(frag)

    t = urllib.parse.unquote(raw_path)
    cand = index.target_to_candidate(cur, t) if t else cur
    new: Optional[str] = None
    if cand is not None and index.exists_in_vault(cand):
        new = ("" if cand == cur else index.relpath_from(cur, cand))
        strategy = "normalize"
        if new == raw_path:
            new = None

    if new is None:
        hit = index.lookup_case_insensitive(cur, lk.target)
        if hit is not None and index.exists_in_vault(hit):
            new, strategy = index.relpath_from(cur, hit), "case"

    if new is None:
        hit = index.lookup_unique_basename(lk.target)
        if hit is not None and hit != cur:
            if not frag or frag in index.headings_for(hit):
                new, strategy = index.relpath_from(cur, hit), "unique-name"

    if new is None and allow_fuzzy:
        hit = index.lookup_fuzzy(cur, lk.target)
        if hit is not None and (not frag or frag in index.headings_for(hit)):
            new, strategy = index.relpath_from(cur, hit), "fuzzy"

    if new is None:
        return None
    new_target = new + (f"#{frag}" if frag else "")
    if new_target == lk.target:
        return None
    return Fix(lk, new_target, strategy)


def apply_fixes(path: Path, fixes: list, dry_run: bool) -> int:
    if not fixes:
        return 0
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return 0
    for fx in sorted(fixes, key=lambda f: f.link.start, reverse=True):
        lk = fx.link
        seg = text[lk.start:lk.end]
        new_seg = seg.replace(lk.target, fx.new_target, 1)
        text = text[:lk.start] + new_seg + text[lk.end:]
    if not dry_run:
        shutil.copy2(path, path.with_name(path.name + BAK_SUFFIX))
        path.write_text(text, encoding="utf-8")
    return len(fixes)


CATEGORY_LABEL = {
    "missing-file": "失效链接",
    "missing-image": "失效图片",
    "missing-anchor": "失效锚点",
    "missing-same-anchor": "失效锚点(本文件)",
}


def _plain_report(issues: list, stats: Stats) -> str:
    out = [f"扫描 {stats.files_scanned} 个文件，检查 {stats.links_checked} 条链接"
           f" / {stats.anchors_checked} 个锚点，发现问题 {stats.broken} 处，"
           f"耗时 {stats.elapsed:.2f}s"]
    for it in issues:
        out.append(f"[{it.level}] {it.file}:{it.line}  {CATEGORY_LABEL.get(it.category, it.category)}"
                   f"  {it.target}  -- {it.detail}"
                   + (f"  => {it.suggestion}" if it.suggestion else ""))
    return "\n".join(out)


def render_report(issues: list, stats: Stats) -> None:
    try:
        from rich.console import Console
        from rich.panel import Panel
        from rich.table import Table
        from rich import box
    except ImportError:
        print(_plain_report(issues, stats))
        return

    console = Console()
    summary = (f"文件 {stats.files_scanned} 个｜链接 {stats.links_checked} 条｜"
               f"问题 {stats.broken} 处｜"
               f"修复 {stats.fixed} 处｜可修复(dry-run) {stats.would_fix} 处｜"
               f"耗时 {stats.elapsed:.2f}s")
    console.print(Panel(summary, title="MDresurrectlink 摘要", style="bold cyan"))

    groups: dict = {}
    for it in issues:
        groups.setdefault(it.category, []).append(it)
    order = ["missing-file", "missing-image", "missing-anchor", "missing-same-anchor"]
    for cat in order + sorted(set(groups) - set(order)):
        if cat not in groups:
            continue
        table = Table(title=CATEGORY_LABEL.get(cat, cat),
                      box=box.SIMPLE, header_style="bold")
        for col in ("文件", "行", "目标", "说明", "建议"):
            table.add_column(col)
        for it in groups[cat]:
            table.add_row(it.file, str(it.line), it.target, it.detail, it.suggestion)
        console.print(table)


def dump_json(issues: list, stats: Stats, out_path: Path) -> None:
    payload = {"stats": asdict(stats),
               "issues": [asdict(i) for i in issues]}
    out_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2),
                        encoding="utf-8")


def collect_markdown_files(root: Path, excludes: list) -> list:
    patterns = [re.compile(fnmatch_translate(g)) for g in excludes]
    files = []
    for p in root.rglob("*"):
        if not p.is_file() or p.suffix.lower() not in (".md", ".markdown", ".mdown"):
            continue
        if any(part in DEFAULT_EXCLUDED_DIRS or part.startswith(".")
               for part in p.relative_to(root).parts[:-1]):
            continue
        if any(rx.search(p.as_posix()) for rx in patterns):
            continue
        files.append(p)
    return sorted(files)


def fnmatch_translate(pat: str) -> str:
    return ".*" + re.escape(pat).replace(r"\*", ".*").replace(r"\?", ".") + ".*"


def load_disk_cache(root: Path) -> dict:
    cp = root / CACHE_FILE
    try:
        return json.loads(cp.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}


def save_disk_cache(root: Path, cache: dict) -> None:
    try:
        (root / CACHE_FILE).write_text(json.dumps(cache), encoding="utf-8")
    except OSError:
        pass


def parse_args(argv=None) -> argparse.Namespace:
    ap = argparse.ArgumentParser(
        prog="mdresurrectlink",
        description="扫描 Markdown 笔记目录，检查相对链接/图片/标题锚点，"
                    "可选自动修复（默认 dry-run）。")
    ap.add_argument("path", type=Path, help="笔记目录")
    ap.add_argument("--fix", action="store_true", help="真正写回修复（自动生成 .bak 备份）")
    ap.add_argument("--dry-run", action="store_true",
                    help="只报告建议修复，不写文件（默认行为）")
    ap.add_argument("--fuzzy", action="store_true",
                    help="允许编辑距离模糊匹配修复（更激进，可能误修）")
    ap.add_argument("--json", metavar="FILE", type=Path, help="把报告导出为 JSON")
    ap.add_argument("--exclude", action="append", default=[], metavar="GLOB",
                    help="排除路径 glob，可重复，如 'archive/*'")
    ap.add_argument("--workers", type=int, default=max(4, (os.cpu_count() or 4) * 4),
                    help="并行线程数（IO 密集，默认 CPU*4）")
    ap.add_argument("--no-cache", action="store_true", help="禁用锚点磁盘缓存")
    ap.add_argument("-v", "--verbose", action="store_true")
    return ap.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    root = args.path.expanduser().resolve()
    if not root.is_dir():
        print(f"错误：目录不存在 {root}", file=sys.stderr)
        return 2

    t0 = time.perf_counter()
    disk_cache = {} if args.no_cache else load_disk_cache(root)
    files = collect_markdown_files(root, args.exclude)
    index = VaultIndex(root, files, disk_cache)
    stats = Stats(files_scanned=len(files))

    all_links: dict = {}
    all_issues: list = []
    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as pool:
        for path, (links, issues) in zip(
                files, pool.map(lambda p: check_file(p, index), files)):
            all_links[path] = links
            all_issues.extend(issues)

    stats.links_checked = sum(len(v) for v in all_links.values())
    stats.anchors_checked = sum(1 for links in all_links.values()
                                for lk in links if "#" in lk.target)

    broken_by_file: dict = {}
    for it in all_issues:
        broken_by_file.setdefault(root / it.file, []).append(it)

    if args.verbose:
        print(f"[verbose] 索引 {len(files)} 文件，缓存命中 "
              f"{len(index._anchors_mem)} 个锚点表", file=sys.stderr)

    fix_map: dict = {}
    for path, links in all_links.items():
        rel = path.relative_to(root).as_posix()
        broken_targets = {i.target for i in broken_by_file.get(path, [])}
        for lk in links:
            if lk.target not in broken_targets:
                continue
            fx = suggest_fix(lk, index, allow_fuzzy=args.fuzzy)
            if fx is None:
                continue
            fix_map.setdefault(path, []).append(fx)
            for it in all_issues:
                if (it.file, it.line, it.target) == (rel, lk.line, lk.target):
                    it.suggestion = f"[{fx.strategy}] {lk.target} -> {fx.new_target}"
                    break

    dry_run = not args.fix
    for path, fixes in fix_map.items():
        n = apply_fixes(path, fixes, dry_run=dry_run)
        if dry_run:
            stats.would_fix += n
        else:
            stats.fixed += n
    if dry_run:
        stats.would_fix = sum(len(v) for v in fix_map.values())
    else:
        stats.fixed = sum(len(v) for v in fix_map.values())

    if not args.no_cache:
        save_disk_cache(root, index.dump_cache())

    stats.broken = len(all_issues)
    stats.elapsed = time.perf_counter() - t0
    render_report(all_issues, stats)
    if args.json:
        dump_json(all_issues, stats, args.json)
        print(f"\nJSON 报告已写入 {args.json}")

    has_error = any(i.level == "error" for i in all_issues)
    return 1 if has_error else 0


if __name__ == "__main__":
    sys.exit(main())
