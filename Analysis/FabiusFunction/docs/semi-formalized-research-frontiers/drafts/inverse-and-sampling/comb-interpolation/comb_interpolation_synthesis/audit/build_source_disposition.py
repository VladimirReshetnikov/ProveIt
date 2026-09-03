#!/usr/bin/env python3
"""Rebuild the exact 180-row pre-retirement file-disposition ledger."""

from __future__ import annotations

import csv
import hashlib
import subprocess
from collections import Counter
from pathlib import Path, PurePosixPath


PACKAGE = Path(__file__).resolve().parents[1]
PIN = PACKAGE / "audit" / "SOURCE_REVISION"
OUTPUT = PACKAGE / "source_disposition.csv"
_ROOT_QUERY = subprocess.run(
    ["git", "-C", str(PACKAGE), "rev-parse", "--show-toplevel"],
    check=True,
    stdout=subprocess.PIPE,
)
REPOSITORY_ROOT = Path(_ROOT_QUERY.stdout.decode("utf-8").strip())
SOURCE_ROOT = PurePosixPath(
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/inverse-and-sampling/comb-interpolation"
)
CANONICAL = SOURCE_ROOT / "comb_interpolation_synthesis"

MAIN_TEX = {
    "Dyadic_Comb_Frontiers/Dyadic_Comb_Frontiers.tex":
        "chapters/03_additive_dyadic.tex",
    "geometric_comb_q_fabius_report/geometric_comb_q_fabius_report.tex":
        "chapters/01_geometric_core.tex",
    "geometric_comb_interpolation_report/geometric_comb_interpolation_report.tex":
        "chapters/02_geometric_extensions.tex",
    "geometric_comb_interpolation_report-3/geometric_comb_interpolation.tex":
        "chapters/02_geometric_extensions.tex",
}
HISTORICAL_LEDGERS = {
    "SHA256SUMS",
    "SHA256SUMS.txt",
}
ADMIN = {
    "MANIFEST.txt",
    "SOURCE_AUDIT.md",
    "CORPUS_AUDIT.md",
    "corpus_manifest.txt",
    "pdf_inspection.txt",
}
PLACEHOLDERS = {
    "corpus_meta.tex",
    "corpus_inventory.tex",
    "generated_results.tex",
}
SHARED_REQUIREMENTS = {
    "Dyadic_Comb_Frontiers/assets/fabius_interpolation_report/requirements.txt",
    "Dyadic_Comb_Frontiers/assets/Fabius_Rvachev_Dyadic_Interpolation_Report/requirements.txt",
}


def git(*arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(REPOSITORY_ROOT), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(arguments)} failed: {detail}")
    return completed.stdout


def destination_for(relative: str) -> tuple[str, str, str, str]:
    path = PurePosixPath(relative)
    name = path.name

    if relative in MAIN_TEX:
        destination = (CANONICAL / MAIN_TEX[relative]).as_posix()
        return (
            "mathematical-manuscript",
            "absorbed-publication",
            destination,
            "Mathematical content is represented in the canonical chapters and theorem concordance.",
        )
    if relative == "README.md":
        return (
            "bookkeeping",
            "canonicalized",
            (SOURCE_ROOT / "README.md").as_posix(),
            "Parent navigation is rewritten to the single canonical volume.",
        )
    if relative == "Dyadic_Comb_Frontiers/README.md":
        return (
            "bookkeeping",
            "canonicalized",
            (CANONICAL / "README.md").as_posix(),
            "The former six/nine-source README is replaced by the full four-manuscript guide.",
        )
    if name.lower().startswith("readme"):
        return (
            "superseded-documentation",
            "canonicalized",
            (CANONICAL / "assets/README.md").as_posix(),
            "Unique replay commands and provenance are distilled into canonical documentation.",
        )
    if name in HISTORICAL_LEDGERS:
        return (
            "historical-checksum-ledger",
            "canonicalized",
            (CANONICAL / "assets/HISTORICAL_LEDGER_AUDIT.csv").as_posix(),
            "The source ledger is stale or package-local; every row and verification outcome is preserved in one audit table.",
        )
    if name in ADMIN:
        return (
            "superseded-administration",
            "canonicalized",
            (CANONICAL / "PROVENANCE.md").as_posix(),
            "Nonduplicative provenance is retained; package-specific wrapper prose is retired.",
        )
    if name in PLACEHOLDERS:
        return (
            "placeholder",
            "retired-placeholder",
            "",
            "The file explicitly says its underlying content was not shipped and supplies no recovered evidence.",
        )
    if name == "Makefile":
        return (
            "broken-build-wrapper",
            "retired-broken-wrapper",
            "",
            "Its publication targets name a removed TeX manuscript; replay commands are documented directly.",
        )
    if path.suffix.lower() == ".pdf":
        if path.parent == PurePosixPath("Dyadic_Comb_Frontiers"):
            return (
                "stale-primary-pdf",
                "replaced-publication",
                (CANONICAL / "comb_interpolation_synthesis.pdf").as_posix(),
                "The stale, visually defective PDF is replaced by the canonical three-pass build.",
            )
        if name in {
            "geometric_comb_interpolation_report.pdf",
            "geometric_comb_interpolation.pdf",
            "geometric_comb_q_fabius_report.pdf",
        }:
            return (
                "stale-primary-pdf",
                "absorbed-publication",
                (CANONICAL / "comb_interpolation_synthesis.pdf").as_posix(),
                "The source report is absorbed; its stale rendering is recoverable from the pinned revision.",
            )
        return (
            "generated-figure-pdf",
            "retired-generated-preview",
            "",
            "The reproducible legacy preview is replaced by retained or regenerated PNG evidence and introduced Type-3 fonts.",
        )
    if relative in SHARED_REQUIREMENTS:
        return (
            "environment-input",
            "retained-deduplicated-evidence",
            (CANONICAL / "assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt").as_posix(),
            "Two byte-identical source rows share one physical payload.",
        )

    if relative.startswith("Dyadic_Comb_Frontiers/assets/"):
        suffix = relative.removeprefix("Dyadic_Comb_Frontiers/assets/")
    else:
        first, slash, rest = relative.partition("/")
        if not slash or first not in {
            "geometric_comb_interpolation_report",
            "geometric_comb_interpolation_report-3",
            "geometric_comb_q_fabius_report",
        }:
            raise ValueError(f"unclassified source path: {relative}")
        suffix = first + "/" + rest
    return (
        "reproducibility-evidence",
        "retained-evidence",
        (CANONICAL / "assets/companion-evidence" / suffix).as_posix(),
        "Unique script, exact data, generated table, environment input, textual output, or diagnostic PNG.",
    )


def main() -> int:
    revision = PIN.read_text(encoding="utf-8").strip()
    revision = git("rev-parse", "--verify", f"{revision}^{{commit}}").decode().strip()
    listing = git(
        "ls-tree",
        "-r",
        "--name-only",
        revision,
        "--",
        ":(top)" + SOURCE_ROOT.as_posix(),
    ).decode("utf-8").splitlines()
    rows: list[dict[str, str]] = []
    for repository_path in listing:
        relative = str(PurePosixPath(repository_path).relative_to(SOURCE_ROOT))
        payload = git("show", f"{revision}:{repository_path}")
        source_class, disposition, destination, reason = destination_for(relative)
        rows.append(
            {
                "source_path": repository_path,
                "sha256": hashlib.sha256(payload).hexdigest(),
                "bytes": str(len(payload)),
                "source_class": source_class,
                "disposition": disposition,
                "destination": destination,
                "reason": reason,
            }
        )
    if len(rows) != 180:
        raise ValueError(f"expected 180 source files, found {len(rows)}")
    keys = [row["source_path"] for row in rows]
    if len(set(keys)) != len(keys):
        raise ValueError("duplicate source path in disposition ledger")
    with OUTPUT.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    print(f"source revision: {revision}")
    print(f"rows: {len(rows)}")
    print("by source class:")
    for key, count in sorted(Counter(row["source_class"] for row in rows).items()):
        print(f"  {key}: {count}")
    print("by disposition:")
    for key, count in sorted(Counter(row["disposition"] for row in rows).items()):
        print(f"  {key}: {count}")
    print(f"wrote: {OUTPUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
