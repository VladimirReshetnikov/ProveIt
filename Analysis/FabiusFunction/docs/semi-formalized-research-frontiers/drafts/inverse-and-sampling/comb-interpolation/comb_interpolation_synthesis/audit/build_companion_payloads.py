#!/usr/bin/env python3
"""Build the companion-payload provenance map.

``COMPANION_PAYLOADS.csv`` has one row per retained source-provenance row,
not merely one row per physical file.  The two byte-identical historical
requirements files therefore remain two auditable rows pointing at one live
payload.  Three PNGs without source-pin PNG counterparts are recorded as
canonical generated assets derived from the pinned figure generator.

Two exact environment files added on main after the immutable 180-file source
pin are checked against the mainline reconciliation revision and recorded
separately.  The source and retained-payload SHA-256 columns in
``COMPANION_PAYLOADS.csv`` are purpose-specific provenance receipts; no
package-wide checksum ledger is produced or checked.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import io
import subprocess
from collections import Counter
from pathlib import Path, PurePosixPath


PACKAGE = Path(__file__).resolve().parents[1]
ASSETS = PACKAGE / "assets"
PIN = PACKAGE / "audit" / "SOURCE_REVISION"
RECONCILIATION_PIN = PACKAGE / "audit" / "MAINLINE_RECONCILIATION_REVISION"
DISPOSITION = PACKAGE / "source_disposition.csv"
OUTPUT = ASSETS / "COMPANION_PAYLOADS.csv"

FIELDS = (
    "entry_kind",
    "source_revision",
    "source_path",
    "source_sha256",
    "source_bytes",
    "source_disposition",
    "live_path",
    "live_sha256",
    "live_bytes",
    "provenance_note",
)

RETAINED = {"retained-evidence", "retained-deduplicated-evidence"}
EXPECTED_SOURCE_ROWS = 106
EXPECTED_SOURCE_PAYLOADS = 105
EXPECTED_GENERATED_ROWS = 3
EXPECTED_MAINLINE_ROWS = 2
EXPECTED_TOTAL_ROWS = (
    EXPECTED_SOURCE_ROWS + EXPECTED_GENERATED_ROWS + EXPECTED_MAINLINE_ROWS
)
EXPECTED_PHYSICAL_PAYLOADS = (
    EXPECTED_SOURCE_PAYLOADS + EXPECTED_GENERATED_ROWS + EXPECTED_MAINLINE_ROWS
)

MAINLINE_FILES = (
    (
        "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
        "drafts/inverse-and-sampling/comb-interpolation/"
        "geometric_comb_interpolation_report/requirements.txt",
        "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
        "drafts/inverse-and-sampling/comb-interpolation/"
        "comb_interpolation_synthesis/assets/companion-evidence/"
        "geometric_comb_interpolation_report/requirements.txt",
    ),
    (
        "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
        "drafts/inverse-and-sampling/comb-interpolation/"
        "geometric_comb_interpolation_report/requirements-lock.txt",
        "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
        "drafts/inverse-and-sampling/comb-interpolation/"
        "comb_interpolation_synthesis/assets/companion-evidence/"
        "geometric_comb_interpolation_report/requirements-lock.txt",
    ),
)

SOURCE_GENERATOR = (
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/inverse-and-sampling/comb-interpolation/Dyadic_Comb_Frontiers/"
    "assets/fabius_interpolation_report/numerical_experiments.py"
)
GENERATED = (
    "fabius_error_profile_N64.png",
    "conditioning_window_N64.png",
    "endpoint_derivative_deficit.png",
)
GENERATED_DIRECTORY = (
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/inverse-and-sampling/comb-interpolation/comb_interpolation_synthesis/"
    "assets/companion-evidence/fabius_interpolation_report/figures"
)
GENERATED_NOTE = (
    "Canonical PNG regenerated with the pinned numerical_experiments.py "
    "--task figures --data-dir data --figure-dir figures workflow, then "
    "rasterized from its generated PDF to remove Type-3-font exposure; the "
    "pinned normalized source tree had no PNG counterpart for this figure."
)


def repository_root() -> Path:
    completed = subprocess.run(
        ["git", "-C", str(PACKAGE), "rev-parse", "--show-toplevel"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return Path(completed.stdout.decode("utf-8").strip())


REPOSITORY = repository_root()


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_revision() -> str:
    requested = PIN.read_text(encoding="utf-8").strip()
    completed = subprocess.run(
        ["git", "-C", str(REPOSITORY), "rev-parse", "--verify", f"{requested}^{{commit}}"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return completed.stdout.decode("utf-8").strip()


def mainline_reconciliation_revision() -> str:
    requested = RECONCILIATION_PIN.read_text(encoding="utf-8").strip()
    completed = subprocess.run(
        ["git", "-C", str(REPOSITORY), "rev-parse", "--verify", f"{requested}^{{commit}}"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return completed.stdout.decode("utf-8").strip()


def disposition_rows() -> list[dict[str, str]]:
    with DISPOSITION.open(newline="", encoding="utf-8") as stream:
        rows = list(csv.DictReader(stream))
    if len(rows) != 180:
        raise ValueError(f"expected 180 source-disposition rows, found {len(rows)}")
    return rows


def live_metadata(repository_path: str) -> tuple[str, str]:
    path = REPOSITORY / PurePosixPath(repository_path)
    if not path.is_file():
        raise ValueError(f"missing live companion payload: {repository_path}")
    return sha256(path), str(path.stat().st_size)


def git_blob_metadata(revision: str, repository_path: str) -> tuple[str, str]:
    completed = subprocess.run(
        ["git", "-C", str(REPOSITORY), "show", f"{revision}:{repository_path}"],
        check=True,
        stdout=subprocess.PIPE,
    )
    payload = completed.stdout
    return hashlib.sha256(payload).hexdigest(), str(len(payload))


def build_rows() -> tuple[str, list[dict[str, str]]]:
    revision = source_revision()
    reconciliation = mainline_reconciliation_revision()
    source = disposition_rows()
    retained = [row for row in source if row["disposition"] in RETAINED]
    if len(retained) != EXPECTED_SOURCE_ROWS:
        raise ValueError(
            f"expected {EXPECTED_SOURCE_ROWS} retained provenance rows, "
            f"found {len(retained)}"
        )
    generator = next(
        (row for row in source if row["source_path"] == SOURCE_GENERATOR),
        None,
    )
    if generator is None:
        raise ValueError(f"missing generator provenance row: {SOURCE_GENERATOR}")

    rows: list[dict[str, str]] = []
    for row in retained:
        digest, size = live_metadata(row["destination"])
        if digest != row["sha256"] or size != row["bytes"]:
            raise ValueError(
                f"retained payload differs from source row: {row['destination']}"
            )
        deduplicated = row["disposition"] == "retained-deduplicated-evidence"
        note = (
            "Byte-identical source row shares the single canonical requirements "
            "payload; both historical provenance rows are retained."
            if deduplicated
            else "Byte-identical payload retained from the pinned source tree."
        )
        rows.append(
            {
                "entry_kind": "pinned-source",
                "source_revision": revision,
                "source_path": row["source_path"],
                "source_sha256": row["sha256"],
                "source_bytes": row["bytes"],
                "source_disposition": row["disposition"],
                "live_path": row["destination"],
                "live_sha256": digest,
                "live_bytes": size,
                "provenance_note": note,
            }
        )

    for name in GENERATED:
        live = f"{GENERATED_DIRECTORY}/{name}"
        digest, size = live_metadata(live)
        rows.append(
            {
                "entry_kind": "canonical-generated",
                "source_revision": revision,
                "source_path": generator["source_path"],
                "source_sha256": generator["sha256"],
                "source_bytes": generator["bytes"],
                "source_disposition": "canonical-generated-from-pinned-script",
                "live_path": live,
                "live_sha256": digest,
                "live_bytes": size,
                "provenance_note": GENERATED_NOTE,
            }
        )

    for source_path, live_path in MAINLINE_FILES:
        source_digest, source_size = git_blob_metadata(
            reconciliation, source_path
        )
        live_digest, live_size = live_metadata(live_path)
        if (source_digest, source_size) != (live_digest, live_size):
            raise ValueError(
                "mainline reconciliation payload differs from source blob: "
                f"{live_path}"
            )
        rows.append(
            {
                "entry_kind": "post-pin-mainline",
                "source_revision": reconciliation,
                "source_path": source_path,
                "source_sha256": source_digest,
                "source_bytes": source_size,
                "source_disposition": "retained-post-pin-evidence",
                "live_path": live_path,
                "live_sha256": live_digest,
                "live_bytes": live_size,
                "provenance_note": (
                    "Exact reproducibility environment added on main after the "
                    "immutable source pin and retained during merge reconciliation."
                ),
            }
        )

    if len(rows) != EXPECTED_TOTAL_ROWS:
        raise ValueError(f"expected {EXPECTED_TOTAL_ROWS} payload rows, found {len(rows)}")
    physical = Counter(row["live_path"] for row in rows)
    if len(physical) != EXPECTED_PHYSICAL_PAYLOADS:
        raise ValueError(
            f"expected {EXPECTED_PHYSICAL_PAYLOADS} physical payloads, "
            f"found {len(physical)}"
        )
    duplicated = {path: count for path, count in physical.items() if count != 1}
    expected_shared = {
        (
            "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
            "drafts/inverse-and-sampling/comb-interpolation/comb_interpolation_synthesis/"
            "assets/companion-evidence/shared/requirements-mpmath-matplotlib.txt"
        ): 2
    }
    if duplicated != expected_shared:
        raise ValueError(
            f"unexpected physical-payload sharing: expected {expected_shared}, "
            f"found {duplicated}"
        )
    return revision, rows


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
        help="compare the ledger with its reproducible contents instead of writing",
    )
    args = parser.parse_args()
    revision, rows = build_rows()
    payload = csv_bytes(rows)

    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_bytes() != payload:
            print(f"FAILED: stale or missing payload ledger: {OUTPUT}")
            return 1
        print(f"companion payload ledger: PASS ({len(rows)} rows)")
    else:
        OUTPUT.write_bytes(payload)
        print(f"wrote: {OUTPUT}")

    print(f"source revision: {revision}")
    print(f"provenance rows: {len(rows)}")
    print(f"physical payloads: {len({row['live_path'] for row in rows})}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
