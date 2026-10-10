#!/usr/bin/env python3
"""Replay this research package without overwriting its supplied data.

Default: four finite exact/symbolic verifiers. --numerical also performs
the high-precision diagnostics and exact bulk-root isolation. --transition
adds the unusually large-index gamma-remainder quadratures. --figures
renders the five figure pairs, using newly computed data when --numerical
is supplied and the bundled data otherwise. All outputs go to the chosen
output directory (default: reproduction/). No network access is used.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
CODE = ROOT / "code"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "reproduction")
    parser.add_argument("--numerical", action="store_true")
    parser.add_argument("--transition", action="store_true")
    parser.add_argument("--figures", action="store_true")
    args = parser.parse_args()
    out = args.output_dir.resolve()
    if out in (ROOT, ROOT / "data", ROOT / "figures"):
        parser.error("Choose a separate output directory to preserve the supplied artifacts.")
    out.mkdir(parents=True, exist_ok=True)
    data = out / "data"
    data.mkdir(exist_ok=True)
    logs = out / "logs"
    logs.mkdir(exist_ok=True)
    receipt = {
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "scope": "Finite certificates and numerical diagnostics; analytic theorems are proved in article.tex.",
        "options": {key: str(value) if isinstance(value, Path) else value
                    for key, value in vars(args).items()},
        "dependencies": {},
        "commands": [],
    }
    for name in ("sympy", "mpmath", "numpy", "matplotlib"):
        try:
            receipt["dependencies"][name] = importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:
            receipt["dependencies"][name] = None

    def run(name, arguments, role):
        command = [sys.executable, str(CODE / name), *map(str, arguments)]
        print(f"Running {name} ({role})", flush=True)
        started = time.monotonic()
        logfile = logs / (Path(name).stem + ".log")
        with logfile.open("w", encoding="utf-8") as stream:
            result = subprocess.run(command, cwd=ROOT, stdout=stream,
                                    stderr=subprocess.STDOUT, check=False)
        entry = {"script": name, "arguments": list(map(str, arguments)),
                 "role": role, "returncode": result.returncode,
                 "seconds": round(time.monotonic() - started, 3),
                 "source_sha256": hashlib.sha256((CODE / name).read_bytes()).hexdigest(),
                 "log": str(logfile.relative_to(out))}
        receipt["commands"].append(entry)
        if result.returncode:
            receipt["status"] = "failed"
            (out / "verification_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
            print(logfile.read_text()[-5000:], file=sys.stderr)
            raise SystemExit(f"{name} failed; see {logfile}")
        print(f"Passed: {name} ({entry['seconds']:.2f} s)", flush=True)

    run("verify_kernel_algebra.py", [data / "kernel_algebra.json"], "exact rational and finite-field certificate")
    run("verify_cohen_c1.py", [data / "cohen_c1_certificate.json"], "exact rational polynomial certificate")
    optional = ["--numeric"] if args.numerical else []
    run("verify_diagonal_inverse.py", [*optional, "--output", data / "diagonal_checks.json"],
        "exact finite identities" + (" and numerical diagnostics" if args.numerical else ""))
    run("verify_cohen_edges.py", [*optional, "--output", data / "cohen_edge_checks.json"],
        "exact finite and symbolic identities" + (" and numerical diagnostics" if args.numerical else ""))
    if args.numerical:
        run("compute_kernel_diagnostics.py", ["--output", data / "kernel_diagnostics.json"], "numerical stationary-point diagnostics")
        run("compute_bulk_root_examples.py", ["--output", data / "bulk_root_examples.json"], "exact rational root isolation")
        run("axis_large_n_diagnostics.py", ["--output", data / "axis_large_n_diagnostics.json"], "numerical gamma quadrature")
    if args.transition:
        run("transition_remainder_diagnostics.py", ["--output", data / "transition_remainder_diagnostics.json"], "numerical normalized gamma quadrature")
    if args.figures:
        figure_data = data if args.numerical else ROOT / "data"
        run("make_figures.py", ["--data-dir", figure_data, "--output-dir", out / "figures",
                                "--samples-output", data / "figure_samples.json"], "figure generation")
    receipt["status"] = "passed"
    receipt["finished_utc"] = datetime.now(timezone.utc).isoformat()
    (out / "verification_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(f"All requested checks completed; receipt: {out / 'verification_receipt.json'}")


if __name__ == "__main__":
    main()
