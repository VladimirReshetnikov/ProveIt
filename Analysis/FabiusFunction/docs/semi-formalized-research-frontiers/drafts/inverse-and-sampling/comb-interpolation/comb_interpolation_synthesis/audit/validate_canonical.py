#!/usr/bin/env python3
"""Fail-closed validation for the canonical comb-interpolation volume.

This is a source audit, not a TeX or Lean build.  It checks the immutable
source projections, the editorial concordance, the live TeX dependency graph,
proof discipline, cross-references, citations, and retained payloads.  It is
intended to run both in the working tree and in a clean checkout.
"""

from __future__ import annotations

import csv
import hashlib
import io
import re
import subprocess
import sys
import tarfile
from collections import Counter
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

import build_historical_ledger_audit as historical
import build_companion_payloads as companion
import build_package_checksums as package_checksums
import build_post_pin_disposition as post_pin
import build_source_disposition as disposition
import build_theorem_concordance as concordance
from extract_source_results import SOURCE_FIELDS


PACKAGE = Path(__file__).resolve().parents[1]
MASTER = PACKAGE / "comb_interpolation_synthesis.tex"
PIN = PACKAGE / "audit" / "SOURCE_REVISION"
CONCORDANCE = PACKAGE / "theorem_concordance.csv"
DISPOSITION = PACKAGE / "source_disposition.csv"
POST_PIN_DISPOSITION = PACKAGE / "post_pin_disposition.csv"
HISTORICAL = PACKAGE / "assets" / "HISTORICAL_LEDGER_AUDIT.csv"

EXPECTED_DISPOSITION_ROWS = 180
EXPECTED_HISTORICAL_ROWS = 151
EXPECTED_HISTORICAL_STATUSES = {
    "match": 68,
    "line-ending-normalized": 34,
    "mismatch": 29,
    "missing": 20,
}

RESULT_KINDS = (
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "identity",
    "conjecture",
    "problem",
    "question",
    "definition",
    "algorithm",
    "example",
    "observation",
)
PROOF_REQUIRED = {"theorem", "proposition", "lemma", "corollary", "identity"}
OPEN_RESULTS = {"conjecture", "problem", "question"}
RESULT_BEGIN_RE = re.compile(
    r"\\begin\{(?P<kind>" + "|".join(RESULT_KINDS) + r")\}"
    r"(?:\[(?P<title>.*?)\])?",
    re.DOTALL,
)
LABEL_RE = re.compile(r"\\label\{([^{}]+)\}")
ENV_RE = re.compile(r"\\(?P<action>begin|end)\{(?P<name>[^{}]+)\}")
REF_RE = re.compile(
    r"\\(?:eqref|ref|pageref|autoref|nameref|cref|Cref|cpageref|Cpageref)"
    r"\*?\s*\{([^{}]+)\}"
)
HYPERREF_RE = re.compile(r"\\hyperref\[([^\]]+)\]")
CITE_RE = re.compile(
    r"\\(?:cite|citep|citet|citealp|citeauthor|Cite|parencite|textcite|nocite)"
    r"\*?(?:\s*\[[^\]]*\]){0,2}\s*\{([^{}]+)\}"
)
BIBITEM_RE = re.compile(r"\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}")
INPUT_RE = re.compile(r"\\(?:input|include)\s*\{([^{}]+)\}")
GRAPHICS_RE = re.compile(
    r"\\includegraphics\*?(?:\s*\[[^\]]*\])?\s*\{([^{}]+)\}"
)
GRAPHICSPATH_RE = re.compile(r"\\graphicspath\s*\{((?:\s*\{[^{}]*\}\s*)+)\}")
PATH_RE = re.compile(r"\\(?:path|nolinkurl)\{([^{}]+)\}")

STALE_PUBLICATION_NAMES = (
    "Dyadic_Comb_Frontiers.tex",
    "Dyadic_Comb_Frontiers.pdf",
    "geometric_comb_interpolation_report.tex",
    "geometric_comb_interpolation_report.pdf",
    "geometric_comb_interpolation.tex",
    "geometric_comb_interpolation.pdf",
    "geometric_comb_q_fabius_report.tex",
    "geometric_comb_q_fabius_report.pdf",
)


@dataclass(frozen=True)
class TeXFile:
    path: Path
    text: str


class Audit:
    def __init__(self) -> None:
        self.failures: list[str] = []
        self.notes: list[str] = []

    def fail(self, message: str) -> None:
        self.failures.append(message)

    def note(self, message: str) -> None:
        self.notes.append(message)

    def finish(self) -> int:
        for note in self.notes:
            print(f"PASS: {note}")
        if self.failures:
            for failure in self.failures[:200]:
                print(f"FAILED: {failure}")
            if len(self.failures) > 200:
                print(f"FAILED: {len(self.failures) - 200} further failures suppressed")
            print(
                f"canonical validation: FAILED "
                f"({len(self.failures)} issue{'s' if len(self.failures) != 1 else ''})"
            )
            return 1
        print("canonical validation: PASS")
        return 0


def git_root() -> Path:
    completed = subprocess.run(
        ["git", "-C", str(PACKAGE), "rev-parse", "--show-toplevel"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return Path(completed.stdout.decode("utf-8").strip())


REPOSITORY = git_root()


def display(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPOSITORY.resolve()).as_posix()
    except ValueError:
        return str(path)


def line_at(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def read_csv(path: Path, audit: Audit) -> tuple[list[str], list[dict[str, str]]]:
    if not path.is_file():
        audit.fail(f"missing CSV: {display(path)}")
        return [], []
    try:
        with path.open(newline="", encoding="utf-8") as stream:
            reader = csv.DictReader(stream)
            fields = reader.fieldnames or []
            rows = list(reader)
    except (OSError, csv.Error, UnicodeError) as error:
        audit.fail(f"cannot read {display(path)}: {error}")
        return [], []
    return fields, rows


def resolve_input(owner: Path, raw: str) -> Path:
    candidate = owner.parent / raw.strip()
    if not candidate.suffix:
        candidate = candidate.with_suffix(".tex")
    return candidate.resolve()


def load_tex_graph(audit: Audit) -> list[TeXFile]:
    ordered: list[TeXFile] = []
    seen: set[Path] = set()
    active: list[Path] = []

    def visit(path: Path) -> None:
        resolved = path.resolve()
        if resolved in active:
            cycle = " -> ".join(display(item) for item in [*active, resolved])
            audit.fail(f"cyclic TeX input graph: {cycle}")
            return
        if resolved in seen:
            return
        if not resolved.is_file():
            audit.fail(f"missing TeX input: {display(resolved)}")
            return
        try:
            raw = resolved.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            audit.fail(f"cannot read TeX input {display(resolved)}: {error}")
            return
        text = concordance.strip_comments(raw)
        seen.add(resolved)
        active.append(resolved)
        ordered.append(TeXFile(resolved, text))
        for match in INPUT_RE.finditer(text):
            value = match.group(1).strip()
            if "\\" in value or "#" in value:
                audit.fail(
                    f"dynamic TeX input is not auditable: "
                    f"{display(resolved)}:{line_at(text, match.start())}: {value}"
                )
                continue
            visit(resolve_input(resolved, value))
        active.pop()

    visit(MASTER)
    audit.note(f"TeX input graph ({len(ordered)} files)")
    return ordered


def validate_environment_balance(files: list[TeXFile], audit: Audit) -> None:
    for source in files:
        stack: list[tuple[str, int]] = []
        for match in ENV_RE.finditer(source.text):
            action = match.group("action")
            name = match.group("name")
            line = line_at(source.text, match.start())
            if action == "begin":
                stack.append((name, line))
            elif not stack:
                audit.fail(f"{display(source.path)}:{line}: unmatched \\end{{{name}}}")
            elif stack[-1][0] != name:
                expected, opened = stack[-1]
                audit.fail(
                    f"{display(source.path)}:{line}: \\end{{{name}}} closes "
                    f"\\begin{{{expected}}} from line {opened}"
                )
                # Recover at this level so one typo does not create hundreds
                # of cascading diagnostics.
                if any(item[0] == name for item in stack):
                    while stack and stack[-1][0] != name:
                        stack.pop()
                    if stack:
                        stack.pop()
            else:
                stack.pop()
        for name, line in stack:
            audit.fail(f"{display(source.path)}:{line}: unclosed \\begin{{{name}}}")
    audit.note("TeX environment balance")


def result_end(text: str, match: re.Match[str]) -> int | None:
    token = rf"\end{{{match.group('kind')}}}"
    end = text.find(token, match.end())
    return None if end < 0 else end + len(token)


def validate_results(files: list[TeXFile], audit: Audit) -> Counter[str]:
    counts: Counter[str] = Counter()
    for source in files:
        matches = list(RESULT_BEGIN_RE.finditer(source.text))
        for index, match in enumerate(matches):
            kind = match.group("kind")
            counts[kind] += 1
            line = line_at(source.text, match.start())
            end = result_end(source.text, match)
            if end is None:
                audit.fail(
                    f"{display(source.path)}:{line}: missing \\end{{{kind}}}"
                )
                continue
            if kind in OPEN_RESULTS and not (match.group("title") or "").strip():
                audit.fail(
                    f"{display(source.path)}:{line}: {kind} needs an explicit title"
                )
            if kind in PROOF_REQUIRED:
                next_start = (
                    matches[index + 1].start() if index + 1 < len(matches) else len(source.text)
                )
                if not re.search(r"\\begin\{proof\}(?:\[[^\]]*\])?", source.text[end:next_start]):
                    title = " ".join((match.group("title") or "untitled").split())
                    audit.fail(
                        f"{display(source.path)}:{line}: {kind} [{title}] has no "
                        "explicit proof before the next result"
                    )
            if kind in PROOF_REQUIRED:
                title = (match.group("title") or "").lower()
                if re.search(r"\b(conjecture|conjectural|open problem|question)\b", title):
                    audit.fail(
                        f"{display(source.path)}:{line}: an open-looking title is "
                        f"misclassified as {kind}"
                    )
    audit.note(
        "result/proof discipline "
        f"({sum(counts.values())} result environments; "
        f"{sum(counts[kind] for kind in PROOF_REQUIRED)} proof-required)"
    )
    return counts


def validate_labels_refs_cites(files: list[TeXFile], audit: Audit) -> set[str]:
    labels: dict[str, tuple[Path, int]] = {}
    references: list[tuple[str, Path, int]] = []
    citations: list[tuple[str, Path, int]] = []
    bibitems: dict[str, tuple[Path, int]] = {}

    for source in files:
        for match in LABEL_RE.finditer(source.text):
            label = match.group(1).strip()
            here = (source.path, line_at(source.text, match.start()))
            if label in labels:
                previous = labels[label]
                audit.fail(
                    f"duplicate label {label!r}: {display(previous[0])}:{previous[1]} "
                    f"and {display(here[0])}:{here[1]}"
                )
            else:
                labels[label] = here
        for regex in (REF_RE, HYPERREF_RE):
            for match in regex.finditer(source.text):
                for key in match.group(1).split(","):
                    references.append(
                        (key.strip(), source.path, line_at(source.text, match.start()))
                    )
        for match in CITE_RE.finditer(source.text):
            for key in match.group(1).split(","):
                if key.strip() != "*":
                    citations.append(
                        (key.strip(), source.path, line_at(source.text, match.start()))
                    )
        for match in BIBITEM_RE.finditer(source.text):
            key = match.group(1).strip()
            here = (source.path, line_at(source.text, match.start()))
            if key in bibitems:
                previous = bibitems[key]
                audit.fail(
                    f"duplicate bibliography key {key!r}: "
                    f"{display(previous[0])}:{previous[1]} and "
                    f"{display(here[0])}:{here[1]}"
                )
            else:
                bibitems[key] = here

    for key, path, line in references:
        if key and key not in labels:
            audit.fail(f"{display(path)}:{line}: unresolved reference {key!r}")
    for key, path, line in citations:
        if key and key not in bibitems:
            audit.fail(f"{display(path)}:{line}: unresolved citation {key!r}")

    audit.note(
        f"cross-references ({len(labels)} unique labels, "
        f"{len(references)} references, {len(bibitems)} bibliography keys)"
    )
    return set(labels)


def graphics_paths(files: list[TeXFile]) -> list[Path]:
    paths = [PACKAGE]
    for source in files:
        for match in GRAPHICSPATH_RE.finditer(source.text):
            for item in re.findall(r"\{([^{}]*)\}", match.group(1)):
                paths.append((PACKAGE / item.strip()).resolve())
    return paths


def validate_assets(files: list[TeXFile], audit: Audit) -> None:
    search = graphics_paths(files)
    extensions = ("", ".pdf", ".png", ".jpg", ".jpeg", ".eps")
    references = 0
    for source in files:
        for match in GRAPHICS_RE.finditer(source.text):
            references += 1
            raw = match.group(1).strip()
            line = line_at(source.text, match.start())
            if "\\" in raw or "#" in raw:
                audit.fail(
                    f"{display(source.path)}:{line}: dynamic graphics path is not auditable: {raw}"
                )
                continue
            suffixes = ("",) if Path(raw).suffix else extensions
            candidates = [base / (raw + suffix) for base in search for suffix in suffixes]
            if not any(path.is_file() for path in candidates):
                audit.fail(
                    f"{display(source.path)}:{line}: missing graphic {raw!r}"
                )

        for match in PATH_RE.finditer(source.text):
            raw = match.group(1).strip().replace("\\", "/")
            if not raw.startswith("assets/"):
                continue
            if any(token in raw for token in ("*", "#", "{", "}", "<", ">")):
                continue
            references += 1
            if not (PACKAGE / PurePosixPath(raw)).exists():
                audit.fail(
                    f"{display(source.path)}:{line_at(source.text, match.start())}: "
                    f"missing asset path {raw!r}"
                )
    audit.note(f"TeX asset references ({references} checked)")


def live_documentation_files(files: list[TeXFile]) -> list[Path]:
    paths = {item.path for item in files if PACKAGE in item.path.parents or item.path == PACKAGE}
    for path in (
        PACKAGE / "README.md",
        PACKAGE / "PROVENANCE.md",
        PACKAGE / "assets" / "README.md",
        PACKAGE / "assets" / "VALIDATION.md",
    ):
        if path.exists():
            paths.add(path.resolve())
    return sorted(paths)


def validate_hygiene(files: list[TeXFile], audit: Audit) -> None:
    marker_re = re.compile(r"TODO|FIXME|<<<<<<<|=======|>>>>>>>", re.IGNORECASE)
    checked = 0
    for path in live_documentation_files(files):
        checked += 1
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            audit.fail(f"cannot read live documentation {display(path)}: {error}")
            continue
        for match in marker_re.finditer(text):
            audit.fail(
                f"{display(path)}:{line_at(text, match.start())}: "
                f"forbidden marker {match.group(0)!r}"
            )
        for stale in STALE_PUBLICATION_NAMES:
            start = 0
            while True:
                offset = text.find(stale, start)
                if offset < 0:
                    break
                audit.fail(
                    f"{display(path)}:{line_at(text, offset)}: stale publication "
                    f"filename {stale!r}"
                )
                start = offset + len(stale)
    audit.note(f"live-document hygiene ({checked} files)")


def source_commit() -> str:
    revision = PIN.read_text(encoding="utf-8").strip()
    return disposition.git("rev-parse", "--verify", f"{revision}^{{commit}}").decode().strip()


def pinned_source_blobs(commit: str) -> dict[str, bytes]:
    completed = subprocess.run(
        [
            "git",
            "-C",
            str(REPOSITORY),
            "archive",
            "--format=tar",
            commit,
            disposition.SOURCE_ROOT.as_posix(),
        ],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    blobs: dict[str, bytes] = {}
    with tarfile.open(fileobj=io.BytesIO(completed.stdout), mode="r:") as archive:
        for member in archive.getmembers():
            if not member.isfile():
                continue
            stream = archive.extractfile(member)
            if stream is None:
                raise ValueError(f"cannot read archived source blob {member.name}")
            blobs[member.name] = stream.read()
    return blobs


def expected_disposition_rows(blobs: dict[str, bytes]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for repository_path in sorted(blobs):
        relative = str(PurePosixPath(repository_path).relative_to(disposition.SOURCE_ROOT))
        payload = blobs[repository_path]
        source_class, action, destination, reason = disposition.destination_for(relative)
        rows.append(
            {
                "source_path": repository_path,
                "sha256": hashlib.sha256(payload).hexdigest(),
                "bytes": str(len(payload)),
                "source_class": source_class,
                "disposition": action,
                "destination": destination,
                "reason": reason,
            }
        )
    return rows


def compare_rows(
    name: str,
    actual: list[dict[str, str]],
    expected: list[dict[str, str]],
    fields: list[str],
    audit: Audit,
) -> None:
    if len(actual) != len(expected):
        audit.fail(f"{name} row count: expected {len(expected)}, found {len(actual)}")
    for number, (found, wanted) in enumerate(zip(actual, expected), start=2):
        for field in fields:
            if found.get(field, "") != wanted.get(field, ""):
                audit.fail(
                    f"{name} row {number} field {field}: "
                    f"expected {wanted.get(field, '')!r}, found {found.get(field, '')!r}"
                )
                break


def validate_source_disposition(blobs: dict[str, bytes], audit: Audit) -> None:
    fields, rows = read_csv(DISPOSITION, audit)
    expected = expected_disposition_rows(blobs)
    expected_fields = list(expected[0]) if expected else []
    if fields != expected_fields:
        audit.fail(
            f"source disposition header: expected {expected_fields!r}, found {fields!r}"
        )
    if len(expected) != EXPECTED_DISPOSITION_ROWS:
        audit.fail(
            f"pinned source tree has {len(expected)} files, expected {EXPECTED_DISPOSITION_ROWS}"
        )
    compare_rows("source disposition", rows, expected, expected_fields, audit)
    if len({row.get("source_path", "") for row in rows}) != len(rows):
        audit.fail("source disposition contains duplicate source paths")

    missing_destinations: set[str] = set()
    for row in rows:
        action = row.get("disposition", "")
        destination = row.get("destination", "")
        if action in {"retained-evidence", "retained-deduplicated-evidence"}:
            target = REPOSITORY / PurePosixPath(destination)
            if not target.is_file():
                audit.fail(f"retained payload is missing: {destination}")
            else:
                digest = hashlib.sha256(target.read_bytes()).hexdigest()
                if digest != row.get("sha256"):
                    audit.fail(
                        f"retained payload hash mismatch: {destination}: "
                        f"expected {row.get('sha256')}, found {digest}"
                    )
        elif destination and action in {
            "canonicalized",
            "absorbed-publication",
            "replaced-publication",
        }:
            if (
                not (REPOSITORY / PurePosixPath(destination)).exists()
                and destination not in missing_destinations
            ):
                missing_destinations.add(destination)
                audit.fail(f"declared canonical destination is missing: {destination}")

    live_source_root = REPOSITORY / disposition.SOURCE_ROOT
    for old in (
        "Dyadic_Comb_Frontiers",
        "geometric_comb_interpolation_report",
        "geometric_comb_interpolation_report-3",
        "geometric_comb_q_fabius_report",
    ):
        if (live_source_root / old).exists():
            audit.fail(f"retired top-level source tree still exists: {(live_source_root / old)}")

    audit.note(
        f"source disposition ({len(rows)} rows; "
        f"{sum(row.get('disposition', '').startswith('retained') for row in rows)} retained rows)"
    )


def validate_post_pin_disposition(audit: Audit) -> None:
    fields, rows = read_csv(POST_PIN_DISPOSITION, audit)
    try:
        source, reconciliation, expected = post_pin.build_rows()
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        audit.fail(f"cannot reproduce post-pin disposition: {error}")
        return
    expected_fields = list(post_pin.FIELDS)
    if fields != expected_fields:
        audit.fail(
            f"post-pin disposition header: expected {expected_fields!r}, found {fields!r}"
        )
    compare_rows("post-pin disposition", rows, expected, expected_fields, audit)
    if len(rows) != 23:
        audit.fail(f"post-pin disposition row count: expected 23, found {len(rows)}")
    if len({row.get("path", "") for row in rows}) != len(rows):
        audit.fail("post-pin disposition contains duplicate paths")

    retained = {
        (row.get("path", ""), row.get("destination", ""))
        for row in rows
        if row.get("disposition") == "retained-post-pin-evidence"
    }
    expected_retained = set(companion.MAINLINE_FILES)
    if retained != expected_retained:
        audit.fail(
            "post-pin retained evidence differs from companion provenance: "
            f"expected {sorted(expected_retained)}, found {sorted(retained)}"
        )
    audit.note(
        f"post-pin reconciliation ({len(rows)} rows; "
        f"{sum(row.get('change_kind') == 'added' for row in rows)} added, "
        f"{sum(row.get('change_kind') == 'modified' for row in rows)} modified; "
        f"{source[:12]} -> {reconciliation[:12]})"
    )


def expected_historical_rows(blobs: dict[str, bytes]) -> list[dict[str, str]]:
    prefix = disposition.SOURCE_ROOT.as_posix() + "/"

    def source_blob(relative: str) -> bytes | None:
        return blobs.get(prefix + relative)

    rows: list[dict[str, str]] = []
    for ledger in historical.LEDGERS:
        payload = source_blob(ledger)
        if payload is None:
            raise ValueError(f"missing pinned source ledger: {ledger}")
        parent = PurePosixPath(ledger).parent
        text = payload.decode("utf-8-sig")
        for number, line in enumerate(text.splitlines(), start=1):
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            match = historical.LINE_RE.match(line)
            if not match:
                raise ValueError(f"{ledger}:{number}: malformed checksum row")
            expected = match.group(1).lower()
            listed = match.group(2).replace("\\", "/")
            while listed.startswith("./"):
                listed = listed[2:]
            target = (parent / listed).as_posix()
            actual_payload = source_blob(target)
            actual = normalized = crlf_normalized = ""
            if actual_payload is None:
                status = "missing"
                note = "The package ledger names a file absent from the pinned normalized tree."
            else:
                actual = hashlib.sha256(actual_payload).hexdigest()
                normalized_payload = actual_payload.replace(b"\r\n", b"\n")
                normalized = hashlib.sha256(normalized_payload).hexdigest()
                crlf_normalized = hashlib.sha256(
                    normalized_payload.replace(b"\n", b"\r\n")
                ).hexdigest()
                if actual == expected:
                    status = "match"
                    note = "Expected and pinned bytes agree."
                elif normalized == expected or crlf_normalized == expected:
                    status = "line-ending-normalized"
                    note = "The expected digest matches after CRLF-to-LF normalization."
                else:
                    status = "mismatch"
                    note = "The pinned file differs substantively or was regenerated after the historical ledger."
            rows.append(
                {
                    "ledger_path": ledger,
                    "ledger_line": str(number),
                    "expected_sha256": expected,
                    "listed_path": listed,
                    "resolved_source_path": target,
                    "status": status,
                    "pinned_sha256": actual,
                    "lf_normalized_sha256": normalized,
                    "crlf_normalized_sha256": crlf_normalized,
                    "note": note,
                }
            )
    return rows


def validate_historical_ledger(blobs: dict[str, bytes], audit: Audit) -> None:
    fields, rows = read_csv(HISTORICAL, audit)
    try:
        expected = expected_historical_rows(blobs)
    except ValueError as error:
        audit.fail(str(error))
        return
    expected_fields = list(expected[0]) if expected else []
    if fields != expected_fields:
        audit.fail(f"historical ledger header: expected {expected_fields!r}, found {fields!r}")
    if len(expected) != EXPECTED_HISTORICAL_ROWS:
        audit.fail(
            f"pinned historical ledger projection has {len(expected)} rows, "
            f"expected {EXPECTED_HISTORICAL_ROWS}"
        )
    compare_rows("historical ledger", rows, expected, expected_fields, audit)
    statuses = Counter(row.get("status", "") for row in rows)
    if dict(statuses) != EXPECTED_HISTORICAL_STATUSES:
        audit.fail(
            f"historical ledger status counts: expected "
            f"{EXPECTED_HISTORICAL_STATUSES}, found {dict(statuses)}"
        )
    audit.note(
        "historical checksum audit "
        f"({len(rows)} rows: 68 exact, 34 line-ending, 29 mismatch, 20 missing)"
    )


def validate_companion_payloads(audit: Audit) -> None:
    fields, rows = read_csv(companion.OUTPUT, audit)
    try:
        _, expected = companion.build_rows()
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        audit.fail(f"cannot reproduce companion-payload ledger: {error}")
        return
    expected_fields = list(companion.FIELDS)
    if fields != expected_fields:
        audit.fail(
            f"companion-payload header: expected {expected_fields!r}, found {fields!r}"
        )
    compare_rows("companion payload", rows, expected, expected_fields, audit)
    if len(rows) != companion.EXPECTED_TOTAL_ROWS:
        audit.fail(
            f"companion payload row count: expected {companion.EXPECTED_TOTAL_ROWS}, "
            f"found {len(rows)}"
        )
    physical = {row.get("live_path", "") for row in rows}
    if len(physical) != companion.EXPECTED_PHYSICAL_PAYLOADS:
        audit.fail(
            f"companion physical-payload count: expected "
            f"{companion.EXPECTED_PHYSICAL_PAYLOADS}, found {len(physical)}"
        )
    expected_files = {
        (REPOSITORY / PurePosixPath(row["live_path"])).resolve() for row in expected
    }
    actual_files = {
        path.resolve()
        for path in (companion.ASSETS / "companion-evidence").rglob("*")
        if path.is_file()
    }
    for path in sorted(expected_files - actual_files):
        audit.fail(f"mapped companion payload is missing: {display(path)}")
    for path in sorted(actual_files - expected_files):
        audit.fail(f"unmapped companion payload is present: {display(path)}")

    audit.note(
        f"companion payloads ({len(rows)} provenance rows, "
        f"{len(expected_files)} physical payloads)"
    )


def validate_package_checksums(audit: Audit) -> None:
    try:
        expected = package_checksums.ledger_bytes()
    except (OSError, RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        audit.fail(f"cannot reproduce package checksum ledger: {error}")
        return
    if not package_checksums.OUTPUT.is_file():
        audit.fail(f"missing package checksum ledger: {display(package_checksums.OUTPUT)}")
        return
    if package_checksums.OUTPUT.read_bytes() != expected:
        audit.fail(f"package checksum ledger is stale: {display(package_checksums.OUTPUT)}")
        return
    rows = expected.decode("utf-8").splitlines()
    if any(line.endswith("  ./SHA256SUMS") for line in rows):
        audit.fail("package checksum ledger incorrectly includes itself")
    audit.note(f"package checksum ledger ({len(rows)} exhaustive rows)")


def validate_concordance(commit: str, labels: set[str], audit: Audit) -> None:
    fields, rows = read_csv(CONCORDANCE, audit)
    try:
        extracted_commit, expected, _ = concordance.build_rows(commit)
        concordance.verify_lean_declarations(expected)
    except (OSError, RuntimeError, ValueError) as error:
        audit.fail(f"cannot reproduce theorem concordance: {error}")
        return
    if extracted_commit != commit:
        audit.fail(
            f"concordance source revision: expected {commit}, found {extracted_commit}"
        )
    expected_fields = list(concordance.ALL_FIELDS)
    if fields != expected_fields:
        audit.fail(f"theorem concordance header: expected {expected_fields!r}, found {fields!r}")
    compare_rows("theorem concordance", rows, expected, expected_fields, audit)
    if len(rows) != concordance.EXPECTED_SOURCE_ROWS:
        audit.fail(
            f"theorem concordance row count: expected "
            f"{concordance.EXPECTED_SOURCE_ROWS}, found {len(rows)}"
        )
    if len({row.get("source_key", "") for row in rows}) != len(rows):
        audit.fail("theorem concordance contains duplicate source keys")

    allowed = {
        "Lean-proved",
        "human-proved frontier result",
        "conjecture",
        "open problem",
        "not applicable",
    }
    for number, row in enumerate(rows, start=2):
        kind = row.get("source_kind", "")
        status = row.get("canonical_status", "")
        label = row.get("canonical_label", "")
        if status not in allowed:
            audit.fail(f"theorem concordance row {number}: invalid status {status!r}")
        if not label:
            audit.fail(f"theorem concordance row {number}: empty canonical label")
        elif label not in labels:
            audit.fail(
                f"theorem concordance row {number}: canonical label {label!r} is absent"
            )
        if not row.get("disposition_notes", "").strip():
            audit.fail(f"theorem concordance row {number}: missing disposition note")
        if kind in concordance.PROVED_KINDS and status not in {
            "Lean-proved",
            "human-proved frontier result",
        }:
            audit.fail(
                f"theorem concordance row {number}: proved-kind {kind} has status {status!r}"
            )
        if kind == "conjecture" and status != "conjecture":
            audit.fail(
                f"theorem concordance row {number}: conjecture has status {status!r}"
            )
        if kind in {"problem", "question"} and status != "open problem":
            audit.fail(
                f"theorem concordance row {number}: {kind} has status {status!r}"
            )
        has_lean = bool(row.get("lean_module") or row.get("lean_declaration"))
        if (status == "Lean-proved") != has_lean:
            audit.fail(
                f"theorem concordance row {number}: Lean status/identifier mismatch"
            )

    # Recompute the immutable source-only digest from the reviewed CSV too;
    # this guards against column-shuffling tricks in an otherwise equal row set.
    source_projection = [{field: row.get(field, "") for field in SOURCE_FIELDS} for row in rows]
    digest = concordance.projection_sha256(source_projection)
    if digest != concordance.EXPECTED_SOURCE_PROJECTION:
        audit.fail(
            f"theorem concordance source digest: expected "
            f"{concordance.EXPECTED_SOURCE_PROJECTION}, found {digest}"
        )
    audit.note(
        f"theorem concordance ({len(rows)} rows; source projection {digest})"
    )


def main() -> int:
    audit = Audit()
    try:
        commit = source_commit()
    except (OSError, RuntimeError, UnicodeError) as error:
        audit.fail(f"cannot resolve SOURCE_REVISION: {error}")
        return audit.finish()
    audit.note(f"pinned source revision {commit}")
    try:
        blobs = pinned_source_blobs(commit)
    except (OSError, subprocess.CalledProcessError, tarfile.TarError, ValueError) as error:
        audit.fail(f"cannot load pinned source archive: {error}")
        return audit.finish()

    files = load_tex_graph(audit)
    validate_environment_balance(files, audit)
    validate_results(files, audit)
    labels = validate_labels_refs_cites(files, audit)
    validate_assets(files, audit)
    validate_hygiene(files, audit)
    validate_source_disposition(blobs, audit)
    validate_post_pin_disposition(audit)
    validate_historical_ledger(blobs, audit)
    validate_companion_payloads(audit)
    validate_concordance(commit, labels, audit)
    validate_package_checksums(audit)
    return audit.finish()


if __name__ == "__main__":
    sys.exit(main())
