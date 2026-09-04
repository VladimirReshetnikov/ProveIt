#!/usr/bin/env python3
"""Replay the canonical representation-volume consolidation audit."""

from __future__ import annotations

import csv
import hashlib
import re
import subprocess
import sys
from pathlib import Path


PACKAGE = Path(__file__).resolve().parents[2]
REPRESENTATIONS = PACKAGE.parent
REPOSITORY = next(parent for parent in PACKAGE.parents if (parent / ".git").exists())
SNAPSHOT = "443793e846934e7363e314ea01129b9f50197a58"
REP_PREFIX = (
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/representations/"
)

CANONICAL_SOURCES = (
    PACKAGE / "Up_Polynomial_Synthesis.tex",
    PACKAGE / "chapters/Lagrange_Cardinal_Loops.tex",
    PACKAGE / "chapters/Legendre_Spectral_Closure.tex",
    PACKAGE / "chapters/Legendre_Transmutation_Arithmetic.tex",
)
THEOREM_KINDS = "theorem|lemma|proposition|corollary"
LEGACY_DIRECTORIES = (
    "rvachev_lagrange_loop_report",
    "Lagrange_Rvachev_Loop_Package",
    "lagrange_rvachev_loop_report_v3",
    "Lagrange_Rvachev_Closed_Loop_Report",
    "Rvachev_Lagrange_Loop_Report_v5",
    "Rvachev_Lagrange_Loop_Report_v6",
    "legendre_rvachev_closed_loop",
    "Legendre_Rvachev_Closed_Loop_Report_v3",
    "Legendre_Rvachev_Closed_Loop_Report_v4",
    "Legendre_Rvachev_Self_Reconstruction",
)
EXPECTED_RETIRED_CHECKSUM_PAYLOADS = 7


def fail(message: str) -> None:
    raise SystemExit(f"consolidation audit failed: {message}")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify_hashes(entries: dict[Path, str], name: str) -> None:
    for path, expected in entries.items():
        if not path.is_file():
            fail(f"{name} target is missing: {path.relative_to(PACKAGE)}")
        actual = digest(path)
        if actual != expected:
            fail(
                f"{name} mismatch for {path.relative_to(PACKAGE)}: "
                f"expected {expected}, got {actual}"
            )


def canonical_assertions() -> tuple[dict[str, str], int, int]:
    environments: dict[str, str] = {}
    proof_count = 0
    conjecture_count = 0
    environment_re = re.compile(
        rf"\\begin\{{({THEOREM_KINDS})\}}(.*?)\\end\{{\1\}}", re.DOTALL
    )
    for source in CANONICAL_SOURCES:
        text = source.read_text(encoding="utf-8")
        proof_count += len(re.findall(r"\\begin\{proof\}", text))
        conjecture_count += len(re.findall(r"\\begin\{conjecture\}", text))
        for kind, body in environment_re.findall(text):
            labels = re.findall(r"\\label\{([^}]+)\}", body)
            if not labels:
                fail(f"{source.name}: unlabeled {kind} environment")
            label = labels[0]
            if label in environments:
                fail(f"duplicate canonical assertion label: {label}")
            environments[label] = kind
    return environments, proof_count, conjecture_count


def verify_crosswalk(environments: dict[str, str]) -> None:
    path = PACKAGE / "assets/provenance/THEOREM_CROSSWALK.md"
    text = path.read_text(encoding="utf-8")
    row_re = re.compile(
        rf"^\|\s*({THEOREM_KINDS})\s+`([^`]+)`\s+—", re.MULTILINE
    )
    rows = row_re.findall(text)
    row_map: dict[str, str] = {}
    for kind, label in rows:
        if label in row_map:
            fail(f"duplicate crosswalk row: {label}")
        row_map[label] = kind
    if row_map != environments:
        missing = sorted(set(environments) - set(row_map))
        extra = sorted(set(row_map) - set(environments))
        mismatched = sorted(
            label
            for label in set(environments) & set(row_map)
            if environments[label] != row_map[label]
        )
        fail(
            f"crosswalk mismatch: missing={missing}, extra={extra}, "
            f"kind_mismatches={mismatched}"
        )


def is_retired_checksum_path(path: str) -> bool:
    name = Path(path).name
    return name == "SHA256SUMS" or name.startswith("SHA256SUMS.")


def verify_companion_payloads() -> tuple[int, int]:
    mapping_path = PACKAGE / "assets/provenance/COMPANION_PAYLOADS.csv"
    with mapping_path.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    if len(rows) != 113:
        fail(f"companion mapping has {len(rows)} rows, expected 113")
    required = {"old_path", "new_path", "sha256", "disposition"}
    if not rows or set(rows[0]) != required:
        fail("companion mapping has the wrong columns")
    old_paths = {row["old_path"] for row in rows}
    new_paths = {row["new_path"] for row in rows}
    if len(old_paths) != 113 or len(new_paths) != 113:
        fail("companion mapping is not one-to-one")
    dispositions = [row["disposition"] for row in rows]
    if dispositions.count("migrated") != 111 or dispositions.count("already-canonical") != 2:
        fail("companion disposition counts are not 111 migrated plus 2 canonical")
    mapped_entries: dict[Path, str] = {}
    retired_checksums = 0
    for row in rows:
        target = (PACKAGE / row["new_path"]).resolve()
        try:
            target.relative_to(PACKAGE)
        except ValueError:
            fail(f"mapped target escapes the package: {row['new_path']}")
        if is_retired_checksum_path(row["new_path"]):
            retired_checksums += 1
            continue
        mapped_entries[target] = row["sha256"]
    if retired_checksums != EXPECTED_RETIRED_CHECKSUM_PAYLOADS:
        fail(
            "retired checksum mapping count is "
            f"{retired_checksums}, expected {EXPECTED_RETIRED_CHECKSUM_PAYLOADS}"
        )
    verify_hashes(mapped_entries, "companion mapping")
    return len(mapped_entries), retired_checksums


def verify_historical_sources() -> int:
    source_map = PACKAGE / "assets/provenance/SOURCE_MAP.csv"
    with source_map.open(newline="", encoding="utf-8") as stream:
        rows = [row for row in csv.DictReader(stream) if row["role"] == "absorbed-source"]
    if len(rows) != 10:
        fail(f"SOURCE_MAP has {len(rows)} absorbed sources, expected 10")
    for row in rows:
        spec = f"{SNAPSHOT}:{REP_PREFIX}{row['old_path']}"
        result = subprocess.run(
            ["git", "show", spec],
            cwd=REPOSITORY,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if result.returncode != 0:
            fail(f"historical source is not recoverable: {spec}")
        actual = hashlib.sha256(result.stdout).hexdigest()
        if actual != row["arrival_sha256"]:
            fail(f"historical source hash mismatch: {row['old_path']}")
    for directory in LEGACY_DIRECTORIES:
        if (REPRESENTATIONS / directory).exists():
            fail(f"retired report directory is still present: {directory}")
    return len(rows)


def main() -> int:
    environments, proofs, conjectures = canonical_assertions()
    if len(environments) != 80 or proofs != 80 or conjectures != 11:
        fail(
            f"canonical counts are assertions={len(environments)}, proofs={proofs}, "
            f"conjectures={conjectures}; expected 80, 80, 11"
    )
    verify_crosswalk(environments)
    payloads, retired_checksums = verify_companion_payloads()
    sources = verify_historical_sources()
    print(
        "consolidation audit passed: "
        f"assertions={len(environments)}, proofs={proofs}, conjectures={conjectures}, "
        f"crosswalk={len(environments)}, companion_payloads={payloads}, "
        f"retired_checksum_rows={retired_checksums}, retired_sources={sources}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
