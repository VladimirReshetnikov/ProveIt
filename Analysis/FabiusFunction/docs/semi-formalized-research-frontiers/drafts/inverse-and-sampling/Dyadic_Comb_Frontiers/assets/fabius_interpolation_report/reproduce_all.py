#!/usr/bin/env python3
"""Rebuild every numerical dataset and figure used by the report.

The individual experiment driver intentionally writes one CSV only after completing a
requested batch.  This orchestrator keeps heavy exact-rational jobs in bounded batches,
then merges them deterministically.  It is cross-platform and uses the current Python
interpreter, so it works on Windows, macOS, and Linux without a shell-specific script.

Usage
-----
    python reproduce_all.py
    python reproduce_all.py --skip-existing

The full run performs exact arithmetic through N=8192 for the endpoint derivative defect
and high-precision grid scans through N=128.  Runtime depends strongly on the Python build
and CPU.  No network access is required.
"""

from __future__ import annotations

import argparse
import csv
import subprocess
import sys
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parent
DRIVER = ROOT / "numerical_experiments.py"
DATA = ROOT / "data"
FIGURES = ROOT / "figures"


def run(arguments: list[str], output: Path | None, skip_existing: bool) -> None:
    """Run one experiment task unless its declared output already exists."""
    if output is not None and skip_existing and output.exists():
        print(f"[skip] {output.relative_to(ROOT)}")
        return
    command = [sys.executable, str(DRIVER), *arguments]
    print("[run]", " ".join(command))
    subprocess.run(command, cwd=ROOT, check=True)


def merge_csv(parts: Iterable[Path], destination: Path, sort_keys: tuple[str, ...]) -> None:
    """Merge homogeneous CSV files, sorting numeric key columns deterministically."""
    rows: list[dict[str, str]] = []
    fieldnames: list[str] | None = None
    for part in parts:
        with part.open(newline="", encoding="utf-8") as stream:
            reader = csv.DictReader(stream)
            if fieldnames is None:
                fieldnames = list(reader.fieldnames or [])
            elif list(reader.fieldnames or []) != fieldnames:
                raise ValueError(f"incompatible columns in {part}")
            rows.extend(reader)
    if not rows or fieldnames is None:
        raise ValueError(f"no rows available for {destination}")
    rows.sort(key=lambda row: tuple(int(row[key]) for key in sort_keys))
    destination.parent.mkdir(parents=True, exist_ok=True)
    with destination.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)
    print(f"[merge] {len(rows)} rows -> {destination.relative_to(ROOT)}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--skip-existing",
        action="store_true",
        help="reuse an existing per-batch CSV instead of recomputing it",
    )
    args = parser.parse_args()
    DATA.mkdir(exist_ok=True)
    FIGURES.mkdir(exist_ok=True)

    run(["--task", "smoke"], None, False)

    run(
        [
            "--task", "predictions", "--N-list", "8,16,32,64,128,256,512,1024",
            "--output", str(DATA / "jet_order_predictions.csv"),
        ],
        DATA / "jet_order_predictions.csv",
        args.skip_existing,
    )
    run(
        [
            "--task", "derivative", "--n-min", "4", "--n-max", "13",
            "--output", str(DATA / "endpoint_derivative_defects.csv"),
        ],
        DATA / "endpoint_derivative_defects.csv",
        args.skip_existing,
    )
    run(
        [
            "--task", "hermite", "--N-list", "4,8,16,32,64", "--grid-level", "12",
            "--output", str(DATA / "hermite_first_derivative.csv"),
        ],
        DATA / "hermite_first_derivative.csv",
        args.skip_existing,
    )

    fabius_batches = [
        (8, 0, 8, "fabius_N8.csv"),
        (16, 0, 10, "fabius_N16.csv"),
        (32, 0, 13, "fabius_N32.csv"),
        (64, 0, 12, "fabius_N64_a.csv"),
        (64, 13, 24, "fabius_N64_b.csv"),
    ]
    for N, m0, m1, filename in fabius_batches:
        output = DATA / filename
        run(
            [
                "--task", "fabius", "--N", str(N), "--m-start", str(m0),
                "--m-end", str(m1), "--grid-level", "12", "--output", str(output),
            ],
            output,
            args.skip_existing,
        )
    merge_csv(
        [DATA / item[3] for item in fabius_batches],
        DATA / "fabius_endpoint_flat.csv",
        ("N", "m"),
    )

    # Pilot values quoted separately in the report.
    for arguments, filename in [
        (["--task", "fabius", "--N", "4", "--m-start", "0", "--m-end", "0",
          "--grid-level", "12"], "fabius_N4_ordinary.csv"),
        (["--task", "fabius", "--N", "128", "--m-start", "0", "--m-end", "0",
          "--grid-level", "11"], "fabius_N128_ordinary.csv"),
        (["--task", "fabius", "--N", "128", "--m-start", "20", "--m-end", "24",
          "--grid-level", "12"], "fabius_N128_selected_jets.csv"),
    ]:
        output = DATA / filename
        run([*arguments, "--output", str(output)], output, args.skip_existing)

    up_batches = [
        (8, 0, 8, "up_N8.csv"),
        (16, 0, 10, "up_N16.csv"),
        (32, 0, 16, "up_N32.csv"),
        (64, 0, 10, "up_N64_a.csv"),
        (64, 11, 20, "up_N64_b.csv"),
    ]
    for N, m0, m1, filename in up_batches:
        output = DATA / filename
        run(
            [
                "--task", "up", "--N", str(N), "--m-start", str(m0),
                "--m-end", str(m1), "--grid-level", "12", "--output", str(output),
            ],
            output,
            args.skip_existing,
        )
    merge_csv(
        [DATA / item[3] for item in up_batches],
        DATA / "up_endpoint_flat.csv",
        ("N", "m"),
    )

    lebesgue_batches = [
        (0, 12, "lebesgue_N64_a.csv"),
        (13, 24, "lebesgue_N64_b.csv"),
    ]
    for m0, m1, filename in lebesgue_batches:
        output = DATA / filename
        run(
            [
                "--task", "lebesgue", "--N", "64", "--m-start", str(m0),
                "--m-end", str(m1), "--grid-level", "11", "--output", str(output),
            ],
            output,
            args.skip_existing,
        )
    merge_csv(
        [DATA / item[2] for item in lebesgue_batches],
        DATA / "lebesgue_N64.csv",
        ("N", "m"),
    )

    run(
        ["--task", "figures", "--data-dir", str(DATA), "--figure-dir", str(FIGURES)],
        None,
        False,
    )
    print("All report data and figures were regenerated successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
