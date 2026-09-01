#!/usr/bin/env python3
"""Build the exact post-pin mainline-reconciliation disposition ledger."""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import subprocess
from collections import Counter
from pathlib import Path, PurePosixPath


PACKAGE = Path(__file__).resolve().parents[1]
SOURCE_PIN = PACKAGE / "audit" / "SOURCE_REVISION"
RECONCILIATION_PIN = PACKAGE / "audit" / "MAINLINE_RECONCILIATION_REVISION"
OUTPUT = PACKAGE / "post_pin_disposition.csv"
_ROOT_QUERY = subprocess.run(
    ["git", "-C", str(PACKAGE), "rev-parse", "--show-toplevel"],
    check=True,
    stdout=subprocess.PIPE,
)
REPOSITORY = Path(_ROOT_QUERY.stdout.decode("utf-8").strip())
SOURCE_ROOT = PurePosixPath(
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/inverse-and-sampling/comb-interpolation"
)
CANONICAL = SOURCE_ROOT / "comb_interpolation_synthesis"

FIELDS = (
    "path",
    "change_kind",
    "reconciliation_sha256",
    "reconciliation_bytes",
    "disposition",
    "destination",
    "note",
)

PROVENANCE = (CANONICAL / "PROVENANCE.md").as_posix()
README = (CANONICAL / "README.md").as_posix()
VALIDATION = (CANONICAL / "assets/VALIDATION.md").as_posix()

CANONICALIZED = {
    "Dyadic_Comb_Frontiers/README.md": README,
    "Dyadic_Comb_Frontiers/assets/fabius_ruffa_phase_calculus/CORPUS_AUDIT.md":
        PROVENANCE,
    "geometric_comb_interpolation_report-3/ARRIVAL_MANIFEST.txt": PROVENANCE,
    "geometric_comb_interpolation_report-3/INTAKE_AUDIT.md": PROVENANCE,
    "geometric_comb_interpolation_report-3/README.md": README,
    "geometric_comb_interpolation_report/ARRIVAL_MANIFEST.txt": PROVENANCE,
    "geometric_comb_interpolation_report/README.md": README,
    "geometric_comb_interpolation_report/REPOSITORY_AUDIT.md": PROVENANCE,
    "geometric_comb_q_fabius_report/INTAKE_AUDIT.md": PROVENANCE,
    "geometric_comb_q_fabius_report/NUMERICAL_REPLAY.txt": PROVENANCE,
    "geometric_comb_q_fabius_report/README.md": README,
}
RETIRED_LEDGERS = {
    "geometric_comb_interpolation_report-3/SHA256SUMS.arrival.txt",
    "geometric_comb_interpolation_report-3/SHA256SUMS.txt",
    "geometric_comb_interpolation_report/SHA256SUMS.arrival.txt",
    "geometric_comb_interpolation_report/SHA256SUMS.txt",
    "geometric_comb_q_fabius_report/ARRIVAL_SHA256SUMS.txt",
    "geometric_comb_q_fabius_report/SHA256SUMS.txt",
}
RETIRED_VALIDATION = {
    "geometric_comb_interpolation_report-3/PDF_VALIDATION.txt",
    "geometric_comb_interpolation_report/PDF_VALIDATION.txt",
    "geometric_comb_q_fabius_report/pdf_preflight.json",
}
RETAINED = {
    "geometric_comb_interpolation_report/requirements-lock.txt": (
        CANONICAL
        / "assets/companion-evidence/geometric_comb_interpolation_report/"
        "requirements-lock.txt"
    ).as_posix(),
    "geometric_comb_interpolation_report/requirements.txt": (
        CANONICAL
        / "assets/companion-evidence/geometric_comb_interpolation_report/"
        "requirements.txt"
    ).as_posix(),
}
ABSORBED = {
    "geometric_comb_interpolation_report/geometric_comb_interpolation_report.tex":
        (CANONICAL / "chapters/02_geometric_extensions.tex").as_posix(),
}

EXPECTED_CHANGE_COUNTS = {"added": 15, "modified": 8}
EXPECTED_DISPOSITION_COUNTS = {
    "absorbed-publication": 1,
    "canonicalized-provenance": 11,
    "retained-post-pin-evidence": 2,
    "retired-artifact-validation": 3,
    "retired-historical-ledger": 6,
}


def git(*arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(REPOSITORY), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(arguments)} failed: {detail}")
    return completed.stdout


def resolve_revision(pin: Path) -> str:
    requested = pin.read_text(encoding="utf-8").strip()
    return git("rev-parse", "--verify", f"{requested}^{{commit}}").decode().strip()


def editorial_disposition(relative: str) -> tuple[str, str, str]:
    if relative in CANONICALIZED:
        return (
            "canonicalized-provenance",
            CANONICALIZED[relative],
            "Nonduplicative conclusions are distilled into the named canonical "
            "record; the original bytes remain recoverable at the reconciliation pin.",
        )
    if relative in RETIRED_LEDGERS:
        return (
            "retired-historical-ledger",
            PROVENANCE,
            "The package-local historical ledger is superseded by canonical "
            "provenance and the exhaustive live package manifest.",
        )
    if relative in RETIRED_VALIDATION:
        return (
            "retired-artifact-validation",
            VALIDATION,
            "Validation of a retired source artifact is superseded by the canonical "
            "validation record; the original remains recoverable from Git.",
        )
    if relative in RETAINED:
        return (
            "retained-post-pin-evidence",
            RETAINED[relative],
            "Exact reproducibility-environment input retained byte-for-byte from "
            "the reconciliation revision.",
        )
    if relative in ABSORBED:
        return (
            "absorbed-publication",
            ABSORBED[relative],
            "The post-pin manuscript change is preamble-only; its mathematical "
            "content remains covered by the canonical chapter and concordance.",
        )
    raise ValueError(f"unclassified post-pin path: {relative}")


def changed_paths(source: str, reconciliation: str) -> dict[str, str]:
    output = git(
        "diff",
        "--name-status",
        "--no-renames",
        source,
        reconciliation,
        "--",
        ":(top)" + SOURCE_ROOT.as_posix(),
    ).decode("utf-8")
    changes: dict[str, str] = {}
    names = {"A": "added", "M": "modified"}
    for line in output.splitlines():
        status, repository_path = line.split("\t", maxsplit=1)
        if status not in names:
            raise ValueError(f"unexpected post-pin change kind {status!r}: {line}")
        relative = PurePosixPath(repository_path).relative_to(SOURCE_ROOT).as_posix()
        if relative in changes:
            raise ValueError(f"duplicate post-pin path: {relative}")
        changes[relative] = names[status]
    return changes


def build_rows() -> tuple[str, str, list[dict[str, str]]]:
    source = resolve_revision(SOURCE_PIN)
    reconciliation = resolve_revision(RECONCILIATION_PIN)
    changes = changed_paths(source, reconciliation)
    classified = set(CANONICALIZED) | RETIRED_LEDGERS | RETIRED_VALIDATION
    classified |= set(RETAINED) | set(ABSORBED)
    if set(changes) != classified:
        missing = sorted(set(changes) - classified)
        extra = sorted(classified - set(changes))
        raise ValueError(
            f"post-pin classification mismatch: unclassified={missing}, stale={extra}"
        )

    rows: list[dict[str, str]] = []
    for relative in sorted(changes):
        repository_path = (SOURCE_ROOT / relative).as_posix()
        payload = git("show", f"{reconciliation}:{repository_path}")
        disposition, destination, note = editorial_disposition(relative)
        rows.append(
            {
                "path": repository_path,
                "change_kind": changes[relative],
                "reconciliation_sha256": hashlib.sha256(payload).hexdigest(),
                "reconciliation_bytes": str(len(payload)),
                "disposition": disposition,
                "destination": destination,
                "note": note,
            }
        )

    change_counts = Counter(row["change_kind"] for row in rows)
    if dict(change_counts) != EXPECTED_CHANGE_COUNTS:
        raise ValueError(
            f"post-pin change counts: expected {EXPECTED_CHANGE_COUNTS}, "
            f"found {dict(change_counts)}"
        )
    dispositions = Counter(row["disposition"] for row in rows)
    if dict(sorted(dispositions.items())) != EXPECTED_DISPOSITION_COUNTS:
        raise ValueError(
            f"post-pin disposition counts: expected {EXPECTED_DISPOSITION_COUNTS}, "
            f"found {dict(sorted(dispositions.items()))}"
        )
    for row in rows:
        destination = REPOSITORY / PurePosixPath(row["destination"])
        if not destination.is_file():
            raise ValueError(f"missing post-pin destination: {row['destination']}")
    return source, reconciliation, rows


def csv_bytes(rows: list[dict[str, str]]) -> bytes:
    stream = io.StringIO(newline="")
    writer = csv.DictWriter(stream, fieldnames=FIELDS, lineterminator="\n")
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue().encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare the ledger with the exact Git-derived projection",
    )
    args = parser.parse_args()
    source, reconciliation, rows = build_rows()
    payload = csv_bytes(rows)
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_bytes() != payload:
            print(f"FAILED: stale or missing post-pin ledger: {OUTPUT}")
            return 1
        print(f"post-pin disposition: PASS ({len(rows)} rows)")
    else:
        OUTPUT.write_bytes(payload)
        print(f"wrote: {OUTPUT}")
    print(f"source revision: {source}")
    print(f"reconciliation revision: {reconciliation}")
    print(f"rows: {len(rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
