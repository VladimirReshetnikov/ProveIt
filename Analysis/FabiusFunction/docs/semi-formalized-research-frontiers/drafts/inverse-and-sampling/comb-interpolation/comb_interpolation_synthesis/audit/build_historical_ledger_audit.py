#!/usr/bin/env python3
"""Audit every row of the eight package-local historical SHA-256 ledgers."""

from __future__ import annotations

import csv
import hashlib
import re
import subprocess
from collections import Counter
from pathlib import Path, PurePosixPath


PACKAGE = Path(__file__).resolve().parents[1]
PIN = PACKAGE / "audit" / "SOURCE_REVISION"
OUTPUT = PACKAGE / "assets" / "HISTORICAL_LEDGER_AUDIT.csv"
SOURCE_ROOT = PurePosixPath(
    "Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/"
    "drafts/inverse-and-sampling/comb-interpolation"
)
LEDGERS = (
    "Dyadic_Comb_Frontiers/assets/fabius_dyadic_comb_report_final/SHA256SUMS.txt",
    "Dyadic_Comb_Frontiers/assets/Fabius_Dyadic_Comb_Sums_Report_Package/SHA256SUMS.txt",
    "Dyadic_Comb_Frontiers/assets/Fabius_Euler_Maclaurin_Report_Package/SHA256SUMS",
    "Dyadic_Comb_Frontiers/assets/fabius_interpolation_report/SHA256SUMS",
    "Dyadic_Comb_Frontiers/assets/Fabius_Rvachev_Dyadic_Interpolation_Report/SHA256SUMS.txt",
    "geometric_comb_interpolation_report/SHA256SUMS.txt",
    "geometric_comb_interpolation_report-3/SHA256SUMS.txt",
    "geometric_comb_q_fabius_report/SHA256SUMS.txt",
)
LINE_RE = re.compile(r"^([0-9a-fA-F]{64})\s+\*?(.*?)\s*$")


def git(*arguments: str) -> bytes:
    completed = subprocess.run(
        ["git", "-C", str(PACKAGE), *arguments],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if completed.returncode:
        detail = completed.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"git {' '.join(arguments)} failed: {detail}")
    return completed.stdout


def blob(revision: str, relative: str) -> bytes | None:
    path = (SOURCE_ROOT / relative).as_posix()
    completed = subprocess.run(
        ["git", "-C", str(PACKAGE), "show", f"{revision}:{path}"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return completed.stdout if completed.returncode == 0 else None


def main() -> int:
    revision = PIN.read_text(encoding="utf-8").strip()
    revision = git("rev-parse", "--verify", f"{revision}^{{commit}}").decode().strip()
    rows: list[dict[str, str]] = []
    for ledger in LEDGERS:
        payload = blob(revision, ledger)
        if payload is None:
            raise ValueError(f"missing source ledger: {ledger}")
        parent = PurePosixPath(ledger).parent
        text = payload.decode("utf-8-sig")
        for line_number, line in enumerate(text.splitlines(), start=1):
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            match = LINE_RE.match(line)
            if not match:
                raise ValueError(f"{ledger}:{line_number}: malformed checksum row")
            expected = match.group(1).lower()
            listed = match.group(2).replace("\\", "/")
            while listed.startswith("./"):
                listed = listed[2:]
            target = (parent / listed).as_posix()
            actual_payload = blob(revision, target)
            actual = ""
            normalized = ""
            crlf_normalized = ""
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
                    "ledger_line": str(line_number),
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
    if len(rows) != 151:
        raise ValueError(f"expected 151 historical rows, found {len(rows)}")
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    with OUTPUT.open("w", encoding="utf-8", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)
    counts = Counter(row["status"] for row in rows)
    print(f"source revision: {revision}")
    print(f"rows: {len(rows)}")
    for status, count in sorted(counts.items()):
        print(f"  {status}: {count}")
    print(f"wrote: {OUTPUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
