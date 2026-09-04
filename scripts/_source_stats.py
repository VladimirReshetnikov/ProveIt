#!/usr/bin/env python3
"""Shared machinery for the committed-source counters in this directory.

`count_lean_code.py` and `count_coq_code.py` are thin front-ends over this
module, so the two reports use exactly the same definitions of "file",
"byte", "line", "comment", and "blank" and can be compared directly.

Scope rules enforced here for every counter:

* Only files **committed** at the given revision (``HEAD`` by default) are
  counted.  Uncommitted edits, staged-but-uncommitted changes, and untracked
  files are ignored; every byte is read from the git object store rather than
  from the working tree, so a dirty checkout cannot skew the numbers.
* **Submodules are not counted.**  ``git ls-tree -r`` does not descend into
  gitlink entries, and this module additionally drops any non-``blob`` entry.
  ProveIt registers several external developments as submodules under
  ``lib/`` (including the Lean project ``lib/FormalizedFormalLogic-Foundation``
  and three Rocq/Coq libraries); none of their code is included.

Line accounting, per file:

    total   every line (a trailing chunk without a final newline still counts)
    blank   whitespace only
    comment lines whose entire non-whitespace content sits inside comments
    code    total - blank - comment

A line carrying both code and a trailing comment counts as code.
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import subprocess
import sys
import threading
from dataclasses import dataclass
from pathlib import Path

# --------------------------------------------------------------------------
# Comment/string scanning
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Syntax:
    """Enough lexical structure to tell comments from code.

    line_comment
        Token that comments out the rest of the line, or ``None`` if the
        language has no line comments (Rocq/Coq).
    block_open / block_close
        Block-comment delimiters.
    nested
        Whether block comments nest (true for both Lean and Rocq/Coq).
    string_delim
        String-literal delimiter, or ``None`` to ignore string literals.
    string_escape
        ``"backslash"`` -- ``\\"`` continues the string (Lean);
        ``"double"``    -- ``""`` continues the string (Rocq/Coq).
    strings_in_comments
        Whether string literals are still recognised inside a block comment.
        Rocq/Coq lexes strings within comments; Lean does not.
    """

    line_comment: str | None
    block_open: str
    block_close: str
    nested: bool = True
    string_delim: str | None = '"'
    string_escape: str = "backslash"
    strings_in_comments: bool = False


LEAN = Syntax(
    line_comment="--",
    block_open="/-",
    block_close="-/",
    nested=True,
    string_delim='"',
    string_escape="backslash",
    strings_in_comments=False,
)

# Rocq/Coq has no line comments; `(* *)` nests, and `""` escapes a quote.
# Character literals are not delimiters in either language here: `'` is a
# legal identifier character in Lean (`h'`) and in Coq notation scopes.
COQ = Syntax(
    line_comment=None,
    block_open="(*",
    block_close="*)",
    nested=True,
    string_delim='"',
    string_escape="double",
    strings_in_comments=True,
)


def analyze(data: bytes, syn: Syntax) -> tuple[int, int, int, bool]:
    """Return ``(lines, blank, comment, final_newline)`` for one source file."""
    if not data:
        return 0, 0, 0, True
    text = data.decode("utf-8", "replace")
    final_newline = text.endswith("\n")
    lines = text.split("\n")
    if final_newline:
        lines.pop()  # the empty piece after the last newline is not a line

    blank = 0
    comment = 0
    depth = 0  # nesting level of block comments
    in_string = False

    for line in lines:
        stripped = line.strip()
        if not stripped and depth == 0 and not in_string:
            blank += 1
            continue

        saw_code = False
        i = 0
        n = len(line)
        while i < n:
            ch = line[i]

            if in_string:
                if syn.string_escape == "backslash" and ch == "\\":
                    i += 2
                    continue
                if ch == syn.string_delim:
                    if syn.string_escape == "double" and line.startswith(
                        syn.string_delim * 2, i
                    ):
                        i += 2
                        continue
                    in_string = False
                i += 1
                continue

            if depth > 0:
                if syn.strings_in_comments and ch == syn.string_delim:
                    in_string = True
                    i += 1
                    continue
                if syn.nested and line.startswith(syn.block_open, i):
                    depth += 1
                    i += len(syn.block_open)
                    continue
                if line.startswith(syn.block_close, i):
                    depth -= 1
                    i += len(syn.block_close)
                    continue
                i += 1
                continue

            # Outside comments and strings.
            if line.startswith(syn.block_open, i):
                depth = 1
                i += len(syn.block_open)
                continue
            if syn.line_comment and line.startswith(syn.line_comment, i):
                break  # rest of the line is a comment
            if syn.string_delim and ch == syn.string_delim:
                in_string = True
                saw_code = True
                i += 1
                continue
            if not ch.isspace():
                saw_code = True
            i += 1

        if not saw_code:
            if stripped:
                comment += 1
            else:
                blank += 1

    return len(lines), blank, comment, final_newline


# --------------------------------------------------------------------------
# Accumulators
# --------------------------------------------------------------------------


@dataclass
class FileStats:
    path: str
    bytes: int
    lines: int
    blank: int
    comment: int
    final_newline: bool

    @property
    def code(self) -> int:
        return self.lines - self.blank - self.comment


@dataclass
class Stats:
    files: int = 0
    bytes: int = 0
    lines: int = 0
    blank: int = 0
    comment: int = 0
    no_final_newline: int = 0

    @property
    def code(self) -> int:
        return self.lines - self.blank - self.comment

    def add(self, other: FileStats) -> None:
        self.files += 1
        self.bytes += other.bytes
        self.lines += other.lines
        self.blank += other.blank
        self.comment += other.comment
        self.no_final_newline += 0 if other.final_newline else 1

    def as_dict(self) -> dict:
        return {
            "files": self.files,
            "bytes": self.bytes,
            "lines": self.lines,
            "code": self.code,
            "comment": self.comment,
            "blank": self.blank,
            "files_without_final_newline": self.no_final_newline,
        }


# --------------------------------------------------------------------------
# git plumbing
# --------------------------------------------------------------------------


def run_git(args: list[str], repo: Path) -> bytes:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if proc.returncode != 0:
        sys.exit(
            f"git {' '.join(args)} failed ({proc.returncode}): "
            f"{proc.stderr.decode('utf-8', 'replace').strip()}"
        )
    return proc.stdout


def default_repo_root() -> Path:
    """The git top level containing these scripts (they live in `scripts/`)."""
    here = Path(__file__).resolve().parent
    proc = subprocess.run(
        ["git", "-C", str(here), "rev-parse", "--show-toplevel"],
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    if proc.returncode == 0:
        return Path(proc.stdout.decode("utf-8", "replace").strip()).resolve()
    return here.parent


def committed_paths(repo: Path, rev: str, extensions: tuple[str, ...]) -> list[str]:
    """Committed files at *rev* with one of *extensions*, excluding submodules."""
    raw = run_git(["ls-tree", "-r", "-z", rev], repo)
    paths: list[str] = []
    for entry in raw.split(b"\0"):
        if not entry:
            continue
        meta, _, name = entry.partition(b"\t")
        fields = meta.split()
        # fields = [mode, type, object]; type "commit" marks a submodule.
        if len(fields) < 2 or fields[1] != b"blob":
            continue
        path = name.decode("utf-8", "surrogateescape")
        if path.endswith(extensions):
            paths.append(path)
    paths.sort()
    return paths


def read_blobs(repo: Path, rev: str, paths: list[str]):
    """Stream file contents out of the object store via one `cat-file --batch`."""
    if not paths:
        return
    proc = subprocess.Popen(
        ["git", "-C", str(repo), "cat-file", "--batch"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
    )
    assert proc.stdin is not None and proc.stdout is not None

    def feed() -> None:
        try:
            for path in paths:
                proc.stdin.write(f"{rev}:{path}\n".encode("utf-8", "surrogateescape"))
            proc.stdin.close()
        except BrokenPipeError:  # pragma: no cover - defensive
            pass

    writer = threading.Thread(target=feed, daemon=True)
    writer.start()

    out = proc.stdout
    for path in paths:
        header = out.readline()
        if not header:
            sys.exit(f"git cat-file ended early at {path}")
        parts = header.split()
        if len(parts) < 3 or parts[1] != b"blob":
            sys.exit(f"unexpected cat-file header for {path}: {header!r}")
        size = int(parts[2])
        data = out.read(size)
        out.read(1)  # trailing newline written after each object
        yield path, data

    writer.join()
    proc.wait()


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------


def fmt(n: int) -> str:
    return f"{n:,}"


def human_bytes(n: int) -> str:
    if n < 1024:
        return f"{n} B"
    value = n / 1024.0
    for unit in ("KiB", "MiB", "GiB"):
        if value < 1024.0 or unit == "GiB":
            return f"{value:,.1f} {unit}"
        value /= 1024.0
    raise AssertionError  # pragma: no cover


COLUMNS = ("files", "bytes", "lines", "code", "comment", "blank")


def print_table(title: str, rows: list[tuple[str, Stats]], label: str) -> None:
    print()
    print(title)
    width = max([len(label)] + [len(name) for name, _ in rows])
    header = f"  {label:<{width}}" + "".join(f"{c:>14}" for c in COLUMNS)
    print(header)
    print("  " + "-" * (len(header) - 2))
    for name, st in rows:
        cells = (st.files, st.bytes, st.lines, st.code, st.comment, st.blank)
        print(f"  {name:<{width}}" + "".join(f"{fmt(v):>14}" for v in cells))


# --------------------------------------------------------------------------
# Front-end driver
# --------------------------------------------------------------------------


def classify(path: str, rules: tuple[tuple[str, tuple[str, ...]], ...]) -> str:
    """First matching rule wins; unmatched files are 'hand-written'."""
    for name, patterns in rules:
        if any(fnmatch.fnmatch(path, pat) for pat in patterns):
            return name
    return "hand-written"


def run(
    *,
    language: str,
    extensions: tuple[str, ...],
    syntax: Syntax,
    rules: tuple[tuple[str, tuple[str, ...]], ...] = (),
    description: str,
    argv: list[str] | None = None,
) -> int:
    parser = argparse.ArgumentParser(description=description)
    parser.add_argument("--rev", default="HEAD", help="revision to measure (default: HEAD)")
    parser.add_argument(
        "--repo",
        default=None,
        help="repository root (default: the git top level containing this script)",
    )
    parser.add_argument(
        "--by-dir",
        type=int,
        default=2,
        metavar="DEPTH",
        help="group the breakdown by the first DEPTH path components (0 disables)",
    )
    parser.add_argument(
        "--top", type=int, default=0, metavar="N", help="also list the N largest files"
    )
    parser.add_argument(
        "--flat", action="store_true", help="do not split the corpus into categories"
    )
    parser.add_argument("--json", action="store_true", help="emit JSON instead of a table")
    args = parser.parse_args(argv)

    repo = Path(args.repo).resolve() if args.repo else default_repo_root()
    paths = committed_paths(repo, args.rev, extensions)

    total = Stats()
    by_category: dict[str, Stats] = {name: Stats() for name, _ in rules}
    by_category.setdefault("hand-written", Stats())
    by_dir: dict[str, Stats] = {}
    per_file: list[FileStats] = []

    for path, data in read_blobs(repo, args.rev, paths):
        lines, blank, comment, final_nl = analyze(data, syntax)
        fs = FileStats(path, len(data), lines, blank, comment, final_nl)
        per_file.append(fs)
        total.add(fs)
        by_category[classify(path, rules)].add(fs)
        if args.by_dir:
            parts = path.split("/")
            key = "/".join(parts[: args.by_dir]) if len(parts) > 1 else "<root>"
            by_dir.setdefault(key, Stats()).add(fs)

    ordered_categories = [("hand-written", by_category["hand-written"])] + [
        (name, by_category[name]) for name, _ in rules
    ]

    if args.json:
        payload = {
            "language": language,
            "extensions": list(extensions),
            "revision": args.rev,
            "revision_sha": run_git(["rev-parse", args.rev], repo).decode().strip(),
            "repository": str(repo),
            "submodules_excluded": True,
            "total": total.as_dict(),
            "by_category": {name: st.as_dict() for name, st in ordered_categories},
            "category_patterns": {name: list(pats) for name, pats in rules},
            "by_directory": {k: v.as_dict() for k, v in sorted(by_dir.items())},
        }
        if args.top:
            payload["largest_files"] = [
                {"path": f.path, "bytes": f.bytes, "lines": f.lines, "code": f.code}
                for f in sorted(per_file, key=lambda f: f.bytes, reverse=True)[: args.top]
            ]
        json.dump(payload, sys.stdout, indent=2)
        print()
        return 0

    sha = run_git(["rev-parse", args.rev], repo).decode().strip()
    branch = run_git(["rev-parse", "--abbrev-ref", "HEAD"], repo).decode().strip()
    exts = ", ".join(f"*{e}" for e in extensions)
    print(f"{language} code committed at {args.rev} ({sha[:12]}, branch {branch})")
    print(f"repository: {repo}")
    print("submodules excluded; working-tree and untracked files not counted")

    print()
    print(f"  {exts} files : {fmt(total.files)}")
    print(f"  bytes       : {fmt(total.bytes)}  ({human_bytes(total.bytes)})")
    print(f"  lines       : {fmt(total.lines)}")
    print(
        f"    code      : {fmt(total.code)}\n"
        f"    comment   : {fmt(total.comment)}\n"
        f"    blank     : {fmt(total.blank)}"
    )
    if total.files:
        print(
            f"  mean file   : {total.bytes / total.files:,.0f} B, "
            f"{total.lines / total.files:,.1f} lines"
        )

    if rules and not args.flat:
        print_table("By category:", ordered_categories, "category")
        for name, pats in rules:
            print(f"  {name} = " + ", ".join(pats))

    if args.by_dir and by_dir:
        rows = sorted(by_dir.items(), key=lambda kv: kv[1].bytes, reverse=True)
        print_table(f"By directory (depth {args.by_dir}):", rows, "path")

    if args.top:
        rows = [
            (f.path, Stats(1, f.bytes, f.lines, f.blank, f.comment, 0))
            for f in sorted(per_file, key=lambda f: f.bytes, reverse=True)[: args.top]
        ]
        print_table(f"Largest {args.top} files:", rows, "path")

    if total.no_final_newline:
        print()
        print(f"note: {fmt(total.no_final_newline)} file(s) lack a final newline")

    return 0
