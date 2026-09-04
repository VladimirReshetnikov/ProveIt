#!/usr/bin/env python3
r"""Validate the canonical Combinatorial Coefficient Calculus package.

The validator deliberately uses only the Python standard library.  Its paths
are anchored at this file, so either of the following invocations works:

    python Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/\
        drafts/combinatorial-coefficient-calculus/\
        Combinatorial_Coefficient_Calculus/validate_canonical.py
    cd Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/\
        drafts/combinatorial-coefficient-calculus/\
        Combinatorial_Coefficient_Calculus
    python validate_canonical.py

The default, transitional mode validates the canonical package while the five
donor packages are still being dispositioned.  ``--final`` additionally
enforces the promised one-document layout, completed source disposition and
provenance records, and removal of stale donor routes from navigation.

Proof/status convention
-----------------------
Every theorem-like or algorithm environment must be followed immediately by
a ``proof`` environment.  A genuinely non-proof item can instead carry one of
these adjacent, machine-readable markers:

    % CANONICAL-PROOF-STATUS: open
    \proofstatus{conjecture}

Accepted status values are intentionally narrow; see ``PROOF_STATUSES`` below.
A ``conjecture`` environment is itself an explicit machine-readable status.
"""

from __future__ import annotations

import argparse
import bisect
import csv
import io
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path, PurePosixPath, PureWindowsPath
from typing import Iterable, Iterator, Sequence


PACKAGE_DIR = Path(__file__).resolve().parent
GROUP_DIR = PACKAGE_DIR.parent
CANONICAL_STEM = "Combinatorial_Coefficient_Calculus"
CANONICAL_TEX = PACKAGE_DIR / f"{CANONICAL_STEM}.tex"
CANONICAL_PDF = PACKAGE_DIR / f"{CANONICAL_STEM}.pdf"

# These are the six independently delivered source syntheses, including the
# directory that survives as the canonical package.
SOURCE_PACKAGES = (
    "Combinatorial_Coefficient_Calculus-2",
    "Combinatorial_Coefficient_Calculus",
    "Combinatorial_Formulae_and_Inversion_Theorems",
    "Unified_Combinatorial_Coefficient_Calculus",
    "Unified_Combinatorial_Formulae",
    "Unified_Combinatorial_Formulae_and_Inversion_Theorems",
)
DONOR_PACKAGES = tuple(name for name in SOURCE_PACKAGES if name != PACKAGE_DIR.name)

DISPOSITION_NAME = "SOURCE_DISPOSITION.csv"
INVENTORY_NAME = "SOURCE_INVENTORY.csv"
SOURCE_IDS = dict(zip(("CCC-2", "CCC", "CFIT", "UCCC", "UCF", "UCFIT"), SOURCE_PACKAGES))

THEOREM_TITLES = {
    "theorem",
    "lemma",
    "proposition",
    "corollary",
    "identity",
    "conjecture",
}
THEOREM_ENVS = set(THEOREM_TITLES) | {"algorithm"}
PROOF_STATUSES = {
    "conjecture",
    "conjectural",
    "open",
    "open-problem",
    "unproved",
    "heuristic",
    "conditional",
    "external",
    "external-result",
    "citation-only",
    "definition-only",
    "specification-only",
    "algorithm-specification",
    "counterexample",
    "refuted",
    "not-claimed",
}
UNRESOLVED_DISPOSITION_WORDS = re.compile(
    r"\b(?:pending|todo|tbd|unreviewed|unresolved|unknown|in[ -]progress|partial)\b",
    re.IGNORECASE,
)

ENV_TOKEN_RE = re.compile(r"\\(?P<kind>begin|end)\s*\{(?P<name>[^{}\s]+)\}")
LABEL_RE = re.compile(r"\\label\s*\{(?P<key>[^{}]+)\}")
REF_RE = re.compile(
    r"\\(?P<command>ref|eqref|autoref|cref|Cref)\*?\s*"
    r"\{(?P<keys>[^{}]*)\}"
)
CITE_RE = re.compile(
    r"\\(?P<command>(?:[A-Za-z]*cite[A-Za-z]*))\*?"
    r"(?:\s*\[[^\[\]]*\]){0,2}\s*\{(?P<keys>[^{}]*)\}"
)
BIBITEM_RE = re.compile(
    r"\\bibitem(?:\s*\[[^\[\]]*\])?\s*\{(?P<key>[^{}]+)\}"
)
NEW_THEOREM_RE = re.compile(
    r"\\newtheorem\*?\s*\{(?P<env>[^{}\s]+)\}"
    r"(?:\s*\[[^\[\]]+\])?\s*"
    r"(?:\{(?P<title>[^{}]+)\}|\[[^\[\]]+\]\s*\{(?P<title2>[^{}]+)\})"
)
CONFLICT_RE = re.compile(r"^(?:<<<<<<<|=======|>>>>>>>)(?:\s.*)?$", re.MULTILINE)
STATUS_COMMENT_RE = re.compile(
    r"^\s*%\s*(?:canonical[-_ ]*)?proof[-_ ]status\s*:\s*"
    r"(?P<status>[A-Za-z][A-Za-z0-9_-]*)\s*$",
    re.IGNORECASE,
)
STATUS_MACRO_RE = re.compile(
    r"\\(?:proofstatus|canonicalproofstatus|frontierstatus)\s*"
    r"\{(?P<status>[A-Za-z][A-Za-z0-9_-]*)\}",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Finding:
    level: str
    code: str
    path: Path
    line: int | None
    message: str


@dataclass
class Counts:
    lines: int = 0
    bytes: int = 0
    environments: int = 0
    statements: int = 0
    adjacent_proofs: int = 0
    status_markers: int = 0
    labels: int = 0
    references: int = 0
    citations: int = 0
    bibitems: int = 0
    disposition_rows: int = 0
    inventory_rows: int = 0


class Report:
    def __init__(self, repo_root: Path) -> None:
        self.repo_root = repo_root
        self.findings: list[Finding] = []
        self.counts = Counts()

    def add(
        self,
        level: str,
        code: str,
        path: Path,
        message: str,
        line: int | None = None,
    ) -> None:
        self.findings.append(Finding(level, code, path, line, message))

    def error(self, code: str, path: Path, message: str, line: int | None = None) -> None:
        self.add("ERROR", code, path, message, line)

    def warning(self, code: str, path: Path, message: str, line: int | None = None) -> None:
        self.add("WARNING", code, path, message, line)

    def display_path(self, path: Path) -> str:
        try:
            return path.resolve().relative_to(self.repo_root.resolve()).as_posix()
        except (OSError, ValueError):
            return str(path)


class SourceMap:
    """Map character offsets to one-based source lines."""

    def __init__(self, text: str) -> None:
        self.newlines = [i for i, char in enumerate(text) if char == "\n"]

    def line(self, offset: int) -> int:
        return bisect.bisect_right(self.newlines, offset) + 1


def locate_repo_root(start: Path) -> Path:
    for candidate in (start, *start.parents):
        if (candidate / ".git").exists():
            return candidate
    # The validator remains useful in an unpacked source tree.  The fallback
    # only affects display paths and SHA-ledger path resolution.
    return start


def read_text(path: Path, report: Report, code: str = "READ") -> str | None:
    try:
        return path.read_text(encoding="utf-8-sig")
    except FileNotFoundError:
        report.error(code, path, "required file is missing")
    except UnicodeDecodeError as exc:
        report.error(code, path, f"file is not valid UTF-8: {exc}")
    except OSError as exc:
        report.error(code, path, f"cannot read file: {exc}")
    return None


def is_escaped(text: str, index: int) -> bool:
    slashes = 0
    cursor = index - 1
    while cursor >= 0 and text[cursor] == "\\":
        slashes += 1
        cursor -= 1
    return slashes % 2 == 1


def strip_comments(text: str) -> str:
    """Replace unescaped TeX comments with spaces, preserving all offsets."""
    chars = list(text)
    cursor = 0
    while cursor < len(chars):
        if chars[cursor] == "%" and not is_escaped(text, cursor):
            end = text.find("\n", cursor)
            if end == -1:
                end = len(chars)
            for index in range(cursor, end):
                chars[index] = " "
            cursor = end
        else:
            cursor += 1
    return "".join(chars)


def strip_verb_material(text: str) -> str:
    """Blank lexical regions whose braces are data rather than TeX groups."""
    chars = list(text)
    verbatim_names = ("verbatim", "Verbatim", "lstlisting", "minted", "pseudo")
    for name in verbatim_names:
        pattern = re.compile(
            rf"\\begin\s*\{{{re.escape(name)}\}}.*?\\end\s*\{{{re.escape(name)}\}}",
            re.DOTALL,
        )
        for match in pattern.finditer(text):
            for index in range(match.start(), match.end()):
                if chars[index] != "\n":
                    chars[index] = " "

    inline_re = re.compile(r"\\verb\*?(?P<delimiter>[^A-Za-z\s])")
    cursor = 0
    current = "".join(chars)
    while True:
        match = inline_re.search(current, cursor)
        if match is None:
            break
        delimiter = match.group("delimiter")
        end = current.find(delimiter, match.end())
        if end == -1:
            # Leave the unmatched command visible; brace checking below will
            # still produce useful diagnostics around it.
            break
        for index in range(match.start(), end + 1):
            if chars[index] != "\n":
                chars[index] = " "
        cursor = end + 1
        current = "".join(chars)
    return "".join(chars)


def split_keys(raw: str) -> list[str]:
    return [key.strip() for key in raw.split(",") if key.strip()]


def duplicates(items: Iterable[tuple[str, int]]) -> dict[str, list[int]]:
    locations: dict[str, list[int]] = {}
    for key, line in items:
        locations.setdefault(key, []).append(line)
    return {key: lines for key, lines in locations.items() if len(lines) > 1}


def validate_conflicts(path: Path, text: str, report: Report) -> None:
    source_map = SourceMap(text)
    for match in CONFLICT_RE.finditer(text):
        report.error(
            "CONFLICT_MARKER",
            path,
            f"unresolved merge marker {match.group(0)!r}",
            source_map.line(match.start()),
        )


def validate_braces(path: Path, clean: str, report: Report) -> None:
    source_map = SourceMap(clean)
    stack: list[int] = []
    for index, char in enumerate(clean):
        if char not in "{}" or is_escaped(clean, index):
            continue
        if char == "{":
            stack.append(index)
        elif stack:
            stack.pop()
        else:
            report.error(
                "BRACE_BALANCE",
                path,
                "closing brace has no matching opening brace",
                source_map.line(index),
            )
    for index in stack[:20]:
        report.error(
            "BRACE_BALANCE",
            path,
            "opening brace has no matching closing brace",
            source_map.line(index),
        )
    if len(stack) > 20:
        report.error(
            "BRACE_BALANCE",
            path,
            f"{len(stack) - 20} additional unmatched opening braces omitted",
        )


def environment_blocks(
    path: Path,
    clean: str,
    report: Report,
) -> list[tuple[str, int, int, int]]:
    """Validate nesting and return (name, begin, end, begin-line) blocks."""
    source_map = SourceMap(clean)
    stack: list[tuple[str, int, int]] = []
    blocks: list[tuple[str, int, int, int]] = []
    begin_counts: dict[str, int] = {}
    end_counts: dict[str, int] = {}

    for token in ENV_TOKEN_RE.finditer(clean):
        kind = token.group("kind")
        name = token.group("name")
        line = source_map.line(token.start())
        if kind == "begin":
            begin_counts[name] = begin_counts.get(name, 0) + 1
            stack.append((name, token.start(), line))
            continue

        end_counts[name] = end_counts.get(name, 0) + 1
        if not stack:
            report.error(
                "ENV_BALANCE",
                path,
                f"\\end{{{name}}} has no matching begin",
                line,
            )
            continue
        open_name, begin, begin_line = stack.pop()
        if open_name != name:
            report.error(
                "ENV_NESTING",
                path,
                f"\\end{{{name}}} closes \\begin{{{open_name}}} from line {begin_line}",
                line,
            )
            # Recover enough to find further problems.  Do not invent a block
            # from mismatched delimiters.
            continue
        blocks.append((name, begin, token.end(), begin_line))

    for name, _begin, line in stack:
        report.error(
            "ENV_BALANCE",
            path,
            f"\\begin{{{name}}} has no matching end",
            line,
        )

    document_begins = begin_counts.get("document", 0)
    document_ends = end_counts.get("document", 0)
    if document_begins != 1 or document_ends != 1:
        report.error(
            "DOCUMENT_ENV",
            path,
            f"expected exactly one document environment; found {document_begins} begin(s) and {document_ends} end(s)",
        )
    report.counts.environments = sum(begin_counts.values())
    return blocks


def theorem_environments(clean: str) -> set[str]:
    environments = set(THEOREM_ENVS)
    for match in NEW_THEOREM_RE.finditer(clean):
        title = (match.group("title") or match.group("title2") or "").strip().lower()
        if title in THEOREM_TITLES or any(
            title.startswith(f"{prefix} ") for prefix in THEOREM_TITLES
        ):
            environments.add(match.group("env"))
    return environments


def adjacent_proof_or_status(raw: str, end: int) -> tuple[str, str | None]:
    """Return ('proof'|'status'|'missing'|'bad-status', status)."""
    cursor = end
    while cursor < len(raw):
        whitespace = re.match(r"\s+", raw[cursor:])
        if whitespace:
            cursor += whitespace.end()
            continue

        if raw[cursor] == "%" and not is_escaped(raw, cursor):
            line_end = raw.find("\n", cursor)
            if line_end == -1:
                line_end = len(raw)
            comment = raw[cursor:line_end]
            status_match = STATUS_COMMENT_RE.match(comment)
            if status_match:
                status = status_match.group("status").lower().replace("_", "-")
                return ("status", status) if status in PROOF_STATUSES else ("bad-status", status)
            cursor = line_end
            continue

        layout = re.match(r"\\(?:par|noindent|smallskip|medskip|bigskip)\b\s*", raw[cursor:])
        if layout:
            cursor += layout.end()
            continue
        break

    if re.match(r"\\begin\s*\{proof\}(?:\s*\[[^\[\]]*\])?", raw[cursor:]):
        return "proof", None
    status_match = STATUS_MACRO_RE.match(raw[cursor:])
    if status_match:
        status = status_match.group("status").lower().replace("_", "-")
        return ("status", status) if status in PROOF_STATUSES else ("bad-status", status)
    return "missing", None


def validate_statement_proofs(
    path: Path,
    raw: str,
    clean: str,
    blocks: Sequence[tuple[str, int, int, int]],
    report: Report,
) -> None:
    theorem_envs = theorem_environments(clean)
    statements = sorted(
        (block for block in blocks if block[0] in theorem_envs),
        key=lambda block: block[1],
    )
    report.counts.statements = len(statements)

    for name, _begin, end, line in statements:
        if name.lower() == "conjecture":
            report.counts.status_markers += 1
            continue
        kind, status = adjacent_proof_or_status(raw, end)
        if kind == "proof":
            report.counts.adjacent_proofs += 1
        elif kind == "status":
            report.counts.status_markers += 1
        elif kind == "bad-status":
            report.error(
                "PROOF_STATUS",
                path,
                f"{name} uses unsupported proof status {status!r}; accepted values: "
                + ", ".join(sorted(PROOF_STATUSES)),
                line,
            )
        else:
            report.error(
                "MISSING_PROOF_STATUS",
                path,
                f"{name} is not followed by a proof or an explicit status marker; "
                "add \\begin{proof}...\\end{proof} or "
                "% CANONICAL-PROOF-STATUS: open",
                line,
            )


def validate_cross_references(path: Path, clean: str, report: Report) -> None:
    source_map = SourceMap(clean)
    labels = [(match.group("key").strip(), source_map.line(match.start())) for match in LABEL_RE.finditer(clean)]
    report.counts.labels = len(labels)
    label_set = {key for key, _line in labels}
    for key, lines in sorted(duplicates(labels).items()):
        report.error(
            "DUPLICATE_LABEL",
            path,
            f"label {key!r} is defined on lines {', '.join(map(str, lines))}",
            lines[1],
        )

    for match in REF_RE.finditer(clean):
        keys = split_keys(match.group("keys"))
        if not keys:
            report.error(
                "EMPTY_REFERENCE",
                path,
                f"\\{match.group('command')} has an empty target",
                source_map.line(match.start()),
            )
        for key in keys:
            report.counts.references += 1
            if key not in label_set:
                report.error(
                    "UNRESOLVED_REFERENCE",
                    path,
                    f"\\{match.group('command')} target {key!r} has no label",
                    source_map.line(match.start()),
                )


def validate_duplicate_crosswalks(
    path: Path,
    clean: str,
    blocks: Sequence[tuple[str, int, int, int]],
    report: Report,
) -> None:
    """Reject repeated crosswalk bodies after comment and whitespace normalization.

    ``clean`` has already passed through ``strip_comments``, preserving source
    offsets and escaped percent signs. Only whole bodies are compared: sharing
    declaration names or other fragments is not a duplication diagnostic.
    """
    opening = re.compile(r"\\begin\s*\{remark\}\s*\[\s*Formal\s+crosswalk\s*\]")
    closing = re.compile(r"\\end\s*\{remark\}$")
    first_lines: dict[str, int] = {}
    for name, begin, end, line in sorted(blocks, key=lambda block: block[1]):
        if name != "remark":
            continue
        match = opening.match(clean, begin, end)
        if match is None:
            continue
        body = " ".join(closing.sub("", clean[match.end():end]).split())
        if body in first_lines:
            report.error(
                "DUPLICATE_FORMAL_CROSSWALK",
                path,
                f"Formal crosswalk repeats the body from line {first_lines[body]} "
                "after removing comments and normalizing whitespace",
                line,
            )
        else:
            first_lines[body] = line


def validate_citations(path: Path, clean: str, report: Report) -> None:
    source_map = SourceMap(clean)
    bibitems = [
        (match.group("key").strip(), source_map.line(match.start()))
        for match in BIBITEM_RE.finditer(clean)
    ]
    report.counts.bibitems = len(bibitems)
    bib_set = {key for key, _line in bibitems}
    for key, lines in sorted(duplicates(bibitems).items()):
        report.error(
            "DUPLICATE_BIBITEM",
            path,
            f"bibliography key {key!r} is defined on lines {', '.join(map(str, lines))}",
            lines[1],
        )

    for match in CITE_RE.finditer(clean):
        command = match.group("command")
        if command.lower() == "citestyle":
            continue
        keys = split_keys(match.group("keys"))
        if not keys:
            report.error(
                "EMPTY_CITATION",
                path,
                f"\\{command} has an empty key list",
                source_map.line(match.start()),
            )
        for key in keys:
            if key == "*" and command.lower() == "nocite":
                continue
            report.counts.citations += 1
            if key not in bib_set:
                report.error(
                    "UNRESOLVED_CITATION",
                    path,
                    f"\\{command} key {key!r} has no unique \\bibitem",
                    source_map.line(match.start()),
                )


def prose_projection(clean: str) -> str:
    text = re.sub(r"\\[A-Za-z@]+\*?", " ", clean)
    text = re.sub(r"\\.", " ", text)
    text = re.sub(r"[{}~$&_^]", " ", text)
    return re.sub(r"\s+", " ", text).strip().lower()


def validate_frontier_disclaimer(path: Path, clean: str, report: Report) -> None:
    prose = prose_projection(clean)
    has_frontier = bool(
        re.search(r"\b(?:research frontier|frontier document|semi[ -]formalized)\b", prose)
    )
    no_machine_claim = bool(
        re.search(
            r"\b(?:no|not|without|does not|do not)\b.{0,180}"
            r"\b(?:lean|machine[ -]checked|formal(?:ized|ised|ization|isation))\b",
            prose,
        )
        or re.search(
            r"\b(?:lean|machine[ -]checked|formal(?:ized|ised|ization|isation))\b"
            r".{0,180}\b(?:no|not|without|does not|do not)\b",
            prose,
        )
    )
    if not has_frontier:
        report.error(
            "FRONTIER_DISCLAIMER",
            path,
            "missing an explicit human-readable statement that this is a research-frontier or semi-formalized document",
        )
    if not no_machine_claim:
        report.error(
            "NO_LEAN_DISCLAIMER",
            path,
            "missing an explicit human-readable statement that the document is not proved/formalized in Lean or machine-checked",
        )


def normalized_header(name: str | None) -> str:
    return re.sub(r"[^a-z0-9]+", "_", (name or "").strip().lower()).strip("_")


def find_metadata(name: str, report: Report, final: bool) -> Path | None:
    candidates = [PACKAGE_DIR / name, GROUP_DIR / name]
    existing = [path for path in candidates if path.exists()]
    if len(existing) > 1:
        report.error(
            "AMBIGUOUS_METADATA",
            PACKAGE_DIR,
            f"{name} exists both in the canonical package and its parent; retain exactly one canonical copy",
        )
        return None
    if existing:
        if existing[0].parent != PACKAGE_DIR:
            report.warning(
                "METADATA_LOCATION",
                existing[0],
                f"move {name} beside the canonical TeX before final publication",
            )
        return existing[0]
    if final:
        report.error("MISSING_METADATA", PACKAGE_DIR / name, "required in --final mode")
    else:
        report.warning("MISSING_METADATA", PACKAGE_DIR / name, "not present yet (allowed during consolidation)")
    return None


def validate_disposition(path: Path, report: Report, final: bool) -> list[dict[str, str]]:
    text = read_text(path, report, "DISPOSITION_READ")
    if text is None:
        return []
    validate_conflicts(path, text, report)
    try:
        reader = csv.DictReader(io.StringIO(text), strict=True)
        original_headers = reader.fieldnames or []
        normalized = [normalized_header(header) for header in original_headers]
        rows = list(reader)
    except csv.Error as exc:
        report.error("DISPOSITION_CSV", path, f"invalid CSV: {exc}")
        return []

    required = {
        "record_id",
        "source_id",
        "source_path",
        "planned_disposition",
        "destination",
        "evidence",
        "status",
    }
    missing = sorted(required - set(normalized))
    if missing:
        report.error(
            "DISPOSITION_SCHEMA",
            path,
            "missing required column(s): " + ", ".join(missing),
            1,
        )
        return []

    report.counts.disposition_rows = len(rows)
    if not rows:
        report.error("DISPOSITION_EMPTY", path, "source disposition contains no records", 1)
        return []

    canonical_rows: list[dict[str, str]] = []
    for row in rows:
        canonical_rows.append(
            {
                normalized[index]: (row.get(header) or "").strip()
                for index, header in enumerate(original_headers)
            }
        )

    ids: dict[str, int] = {}
    incomplete: list[tuple[int, str]] = []
    for line, row in enumerate(canonical_rows, start=2):
        record_id = row["record_id"]
        if not record_id:
            report.error("DISPOSITION_ID", path, "record_id is empty", line)
        elif record_id in ids:
            report.error(
                "DISPOSITION_ID",
                path,
                f"record_id {record_id!r} duplicates line {ids[record_id]}",
                line,
            )
        else:
            ids[record_id] = line

        for field in ("source_id", "source_path", "planned_disposition", "status"):
            if not row[field]:
                report.error("DISPOSITION_FIELD", path, f"{field} is empty", line)

        combined = " | ".join(row.values())
        if UNRESOLVED_DISPOSITION_WORDS.search(combined):
            incomplete.append((line, record_id or "<missing-id>"))
        if final:
            for field in ("destination", "evidence"):
                if not row[field]:
                    report.error(
                        "DISPOSITION_FINAL_FIELD",
                        path,
                        f"{field} is empty in final disposition row {record_id!r}",
                        line,
                    )

    all_text = "\n".join(" | ".join(row.values()) for row in canonical_rows)
    for source in SOURCE_PACKAGES:
        if source not in all_text:
            report.error(
                "DISPOSITION_COVERAGE",
                path,
                f"no disposition record identifies source package {source!r}",
            )

    if incomplete:
        sample = ", ".join(f"{record_id} (line {line})" for line, record_id in incomplete[:12])
        suffix = "" if len(incomplete) <= 12 else f"; {len(incomplete) - 12} more"
        message = f"{len(incomplete)} unresolved disposition row(s): {sample}{suffix}"
        if final:
            report.error("DISPOSITION_INCOMPLETE", path, message)
        else:
            report.warning("DISPOSITION_INCOMPLETE", path, message)
    return canonical_rows


def safe_relative_path(value: str) -> bool:
    """Accept portable repository paths, excluding drive and traversal syntax."""
    posix = PurePosixPath(value)
    windows = PureWindowsPath(value)
    return bool(value) and not (
        posix.is_absolute()
        or windows.drive
        or windows.root
        or "\\" in value
        or ":" in value
        or any(part in {"", ".", ".."} for part in value.split("/"))
    )


def validate_inventory(
    path: Path, report: Report, disposition: list[dict[str, str]]
) -> None:
    """Check original-source provenance through Git, without mutable digests."""
    text = read_text(path, report, "INVENTORY_READ")
    if text is None:
        return
    validate_conflicts(path, text, report)
    fields = (
        "source_id", "source_package", "snapshot_commit", "tex_path", "pdf_path",
        "archive_blob", "tex_member", "pdf_member",
    )
    try:
        reader = csv.DictReader(io.StringIO(text), strict=True)
        if reader.fieldnames != list(fields):
            report.error("INVENTORY_SCHEMA", path, "expected columns: " + ", ".join(fields), 1)
            return
        rows = list(reader)
    except csv.Error as exc:
        report.error("INVENTORY_CSV", path, f"invalid CSV: {exc}")
        return

    report.counts.inventory_rows = len(rows)
    seen: set[str] = set()
    objects: list[tuple[str, str, int]] = []
    group_path = GROUP_DIR.relative_to(report.repo_root).as_posix()
    for line, row in enumerate(rows, start=2):
        if None in row or any(row.get(field) is None for field in fields):
            report.error("INVENTORY_COLUMNS", path, "row does not have exactly eight fields", line)
            continue
        row = {field: row[field].strip() for field in fields}
        source_id = row["source_id"]
        if source_id not in SOURCE_IDS or source_id in seen:
            report.error("INVENTORY_ID", path, f"unknown or duplicate source_id {source_id!r}", line)
            continue
        seen.add(source_id)
        package = SOURCE_IDS[source_id]
        stem = CANONICAL_STEM if source_id == "CCC-2" else package
        if row["source_package"] != package:
            report.error("INVENTORY_PACKAGE", path, f"{source_id} must identify {package!r}", line)
        commit = row["snapshot_commit"]
        archive = row["archive_blob"]
        for field, value in (("snapshot_commit", commit), ("archive_blob", archive)):
            if not re.fullmatch(r"[0-9a-f]{40}", value):
                report.error("INVENTORY_GIT_ID", path, f"{field} must be a full immutable Git object ID", line)
        if re.fullmatch(r"[0-9a-f]{40}", commit):
            objects.append((commit, "commit", line))
        if re.fullmatch(r"[0-9a-f]{40}", archive):
            objects.append((archive, "blob", line))
        for kind in ("tex", "pdf"):
            relative = row[f"{kind}_path"]
            member = row[f"{kind}_member"]
            expected_member = f"{stem}.{kind}"
            expected_path = f"{group_path}/{package}/{expected_member}"
            if not safe_relative_path(relative) or relative != expected_path:
                report.error("INVENTORY_PATH", path, f"expected repository path {expected_path!r}", line)
            elif re.fullmatch(r"[0-9a-f]{40}", commit):
                objects.append((f"{commit}:{relative}", "blob", line))
            if not safe_relative_path(member) or member != expected_member:
                report.error("INVENTORY_MEMBER", path, f"expected flat archive member {expected_member!r}", line)
        source_rows = [item for item in disposition if item.get("record_id") == f"SRC-{source_id}"]
        if len(source_rows) != 1 or (
            source_rows[0].get("source_id") != source_id
            or source_rows[0].get("source_path") != f"{package}/{stem}.tex"
        ):
            report.error("INVENTORY_DISPOSITION", path, f"{source_id} lacks its matching source-disposition row", line)

    missing = sorted(SOURCE_IDS.keys() - seen)
    if missing:
        report.error("INVENTORY_COVERAGE", path, "missing original source(s): " + ", ".join(missing))
    if objects:
        try:
            result = subprocess.run(
                ["git", "cat-file", "--batch-check=%(objecttype)"],
                cwd=report.repo_root,
                input="".join(f"{identity}\n" for identity, _kind, _line in objects),
                capture_output=True, text=True, check=True, timeout=30,
            )
        except (OSError, subprocess.SubprocessError) as exc:
            report.error("INVENTORY_GIT_READ", path, f"cannot verify original Git objects: {exc}")
            return
        types = result.stdout.splitlines()
        if len(types) != len(objects):
            report.error("INVENTORY_GIT_READ", path, "Git returned an incomplete object inventory")
            return
        for (identity, expected_type, line), actual_type in zip(objects, types):
            if actual_type != expected_type:
                report.error("INVENTORY_GIT_OBJECT", path, f"{identity!r} is not an available Git {expected_type}", line)


def navigation_files() -> Iterator[Path]:
    candidates = (
        GROUP_DIR / "README.md",
        GROUP_DIR.parent / "MANIFEST.md",
        GROUP_DIR.parent / "incoming" / "README.md",
    )
    yield from (path for path in candidates if path.is_file())


def validate_final_layout(report: Report) -> None:
    for donor in DONOR_PACKAGES:
        donor_path = GROUP_DIR / donor
        if donor_path.exists():
            report.error(
                "DONOR_REMAINS",
                donor_path,
                "donor package remains; delete it only after its completed disposition is recorded",
            )

    tex_files = sorted(GROUP_DIR.rglob("*.tex"))
    pdf_files = sorted(GROUP_DIR.rglob("*.pdf"))
    if tex_files != [CANONICAL_TEX]:
        report.error(
            "FINAL_TEX_LAYOUT",
            GROUP_DIR,
            "--final requires exactly one TeX document under the group; found: "
            + (", ".join(report.display_path(path) for path in tex_files) or "none"),
        )
    if pdf_files != [CANONICAL_PDF]:
        report.error(
            "FINAL_PDF_LAYOUT",
            GROUP_DIR,
            "--final requires exactly one matching PDF under the group; found: "
            + (", ".join(report.display_path(path) for path in pdf_files) or "none"),
        )

    for nav_path in navigation_files():
        text = read_text(nav_path, report, "NAVIGATION_READ")
        if text is None:
            continue
        validate_conflicts(nav_path, text, report)
        source_map = SourceMap(text)
        normalized = text.replace("\\", "/")
        for donor in DONOR_PACKAGES:
            # Plain historical names are legitimate provenance.  What final
            # navigation must not retain is a route into a directory that was
            # deleted: either a full group path or a relative donor/path.
            route_re = re.compile(
                rf"(?:combinatorial-coefficient-calculus/)?{re.escape(donor)}/"
            )
            for match in route_re.finditer(normalized):
                report.error(
                    "STALE_DONOR_ROUTE",
                    nav_path,
                    f"navigation still routes to deleted donor directory {donor!r}",
                    source_map.line(match.start()),
                )


def validate_register_totals(path: Path, clean: str, report: Report) -> None:
    """Check the register's advertised totals against its actual status rows.

    This is an accounting check, not validation that a cited Lean theorem
    proves the human statement. Unlabelled rows count just like labelled ones.
    """
    marker = r"\section{Lean formalization register}"
    start = clean.find(marker)
    if start < 0:
        report.error("LEAN_REGISTER_MISSING", path, "missing Lean formalization register")
        return
    register = clean[start:].split(r"\backmatter", 1)[0]
    summary = re.search(
        r"Current totals:\s*(\d+) Lean,\s*(\d+) partial,\s*(\d+) none,"
        r"\s*of (\d+) results\.", register,
    )
    if summary is None:
        report.error("LEAN_REGISTER_SUMMARY", path, "missing or malformed register totals",
                     SourceMap(clean).line(start))
        return
    rows = Counter(re.findall(r"(?m)^.*? & (Lean|partial|none) & ", register))
    actual = (rows["Lean"], rows["partial"], rows["none"], sum(rows.values()))
    advertised = tuple(map(int, summary.groups()))
    if advertised != actual:
        report.error(
            "LEAN_REGISTER_TOTALS", path,
            f"advertised Lean/partial/none/total {advertised}, but actual rows are {actual}",
            SourceMap(clean).line(start + summary.start()),
        )


def validate_package(final: bool) -> Report:
    repo_root = locate_repo_root(PACKAGE_DIR)
    report = Report(repo_root)

    package_tex = sorted(PACKAGE_DIR.glob("*.tex"))
    if package_tex != [CANONICAL_TEX]:
        report.error(
            "CANONICAL_TEX_LAYOUT",
            PACKAGE_DIR,
            f"expected exactly one package TeX named {CANONICAL_TEX.name}; found: "
            + (", ".join(path.name for path in package_tex) or "none"),
        )

    raw = read_text(CANONICAL_TEX, report, "CANONICAL_TEX_READ")
    if raw is not None:
        report.counts.lines = len(raw.splitlines())
        report.counts.bytes = len(raw.encode("utf-8"))
        validate_conflicts(CANONICAL_TEX, raw, report)
        clean = strip_comments(raw)
        brace_clean = strip_verb_material(clean)
        validate_braces(CANONICAL_TEX, brace_clean, report)
        blocks = environment_blocks(CANONICAL_TEX, clean, report)
        validate_cross_references(CANONICAL_TEX, clean, report)
        validate_duplicate_crosswalks(CANONICAL_TEX, clean, blocks, report)
        validate_citations(CANONICAL_TEX, clean, report)
        validate_statement_proofs(CANONICAL_TEX, raw, clean, blocks, report)
        validate_frontier_disclaimer(CANONICAL_TEX, clean, report)
        validate_register_totals(CANONICAL_TEX, clean, report)

    disposition_rows: list[dict[str, str]] = []
    disposition = find_metadata(DISPOSITION_NAME, report, final)
    if disposition is not None:
        disposition_rows = validate_disposition(disposition, report, final)
    inventory = find_metadata(INVENTORY_NAME, report, final)
    if inventory is not None:
        validate_inventory(inventory, report, disposition_rows)

    if final:
        validate_final_layout(report)

    return report


def print_report(report: Report, final: bool) -> None:
    errors = sum(finding.level == "ERROR" for finding in report.findings)
    warnings = sum(finding.level == "WARNING" for finding in report.findings)
    mode = "final" if final else "transitional"
    counts = report.counts

    print("Canonical Combinatorial Coefficient Calculus validation")
    print(f"mode: {mode}")
    print(f"package: {report.display_path(PACKAGE_DIR)}")
    print(f"canonical TeX: {CANONICAL_TEX.name}")
    print("counts:")
    print(f"  TeX: {counts.lines} lines, {counts.bytes} UTF-8 bytes")
    print(f"  environments: {counts.environments}")
    print(
        "  theorem-like/algorithm items: "
        f"{counts.statements} ({counts.adjacent_proofs} adjacent proofs, "
        f"{counts.status_markers} explicit statuses)"
    )
    print(f"  labels/references: {counts.labels}/{counts.references}")
    print(f"  bibliography items/citations: {counts.bibitems}/{counts.citations}")
    print(f"  source-disposition rows: {counts.disposition_rows}")
    print(f"  original-source inventory rows: {counts.inventory_rows}")

    for finding in sorted(
        report.findings,
        key=lambda item: (
            0 if item.level == "ERROR" else 1,
            report.display_path(item.path),
            item.line or 0,
            item.code,
        ),
    ):
        location = report.display_path(finding.path)
        if finding.line is not None:
            location += f":{finding.line}"
        print(f"{finding.level} [{finding.code}] {location}: {finding.message}")

    result = "PASS" if errors == 0 else "FAIL"
    print(f"RESULT: {result} ({errors} error(s), {warnings} warning(s))")


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--final",
        action="store_true",
        help="enforce completed disposition, one-package layout, and navigation cleanup",
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    report = validate_package(args.final)
    print_report(report, args.final)
    return 0 if all(finding.level != "ERROR" for finding in report.findings) else 1


if __name__ == "__main__":
    raise SystemExit(main())
