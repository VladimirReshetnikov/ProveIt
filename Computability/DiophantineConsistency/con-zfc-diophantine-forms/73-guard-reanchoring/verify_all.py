#!/usr/bin/env python3
"""Offline standard-library finite audits; not a consistency search."""
from __future__ import annotations
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    mode = "optimized" if sys.flags.optimize else "normal"
    target = ROOT / "validation"
    logs = target / mode
    logs.mkdir(parents=True, exist_ok=True)
    python = [sys.executable] + (["-O"] if sys.flags.optimize else [])
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    immutable_outputs = [
        "integer34/sextic34.json",
        "integer34/sextic34_compact.json",
        "positive/p13_degree30.json",
        "positive/p12_centered_product_split2.json",
        "positive/p12_centered_sos_split2.json",
    ]
    before = {p: digest(ROOT / p) for p in immutable_outputs}
    jobs = [
        ("build_integer34", ["integer34/build_sextic34.py"]),
        ("check_integer34", ["integer34/verify_sextic34.py"]),
        ("bind_compact_integer34", ["integer34/build_compact_instance.py"]),
        ("compact_coefficients", ["compact_coefficients/verify.py", "--receipt",
                                 f"validation/compact_{mode}.json"]),
        ("build_original_coefficients", ["integer_coefficients/build_coefficients.py"]),
        ("check_original_coefficients", ["integer_coefficients/verify_coefficients.py"]),
        ("compact_integer_adapter", ["integer34/verify_compact_adapter.py"]),
        ("build_positive13", ["positive/build_adaptive13.py"]),
        ("build_positive12", ["positive/build_centered12.py"]),
        ("check_positive", ["positive/check_new.py"]),
        ("reusable_lemmas", ["research/verify_reusable_lemmas.py", "--output",
                            f"validation/reusable_{mode}.json"]),
    ]
    receipts = []
    for name, arguments in jobs:
        start = time.monotonic()
        proc = subprocess.run(
            python + arguments, cwd=ROOT, env=environment,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
            check=False,
        )
        path = logs / (name + ".log")
        path.write_text(proc.stdout, encoding="utf-8")
        receipts.append({
            "name": name, "arguments": arguments, "exit_code": proc.returncode,
            "elapsed_seconds": round(time.monotonic() - start, 3),
            "log": path.relative_to(ROOT).as_posix(),
            "log_sha256": digest(path),
        })
        print(("PASS" if proc.returncode == 0 else "FAIL") + " " + name, flush=True)
        if proc.returncode:
            print(proc.stdout[-6000:], file=sys.stderr)
            break
    after = {p: digest(ROOT / p) for p in immutable_outputs}
    reproducible = before == after
    success = (len(receipts) == len(jobs)
               and all(r["exit_code"] == 0 for r in receipts) and reproducible)
    result = {
        "status": "PASS" if success else "FAIL",
        "python": sys.version, "optimized": bool(sys.flags.optimize),
        "offline": True, "standard_library_only": True,
        "literal_builders_reproduce_delivered_bytes": reproducible,
        "literal_sha256": after, "checks": receipts,
        "scope": (
            "Exact finite algebra, metrics, coefficient reconstruction and "
            "provenance. Universal Pell, native compiler and ZFC refutation "
            "equivalences are supplied by the written and inherited proofs."
        ),
    }
    (target / f"VERIFICATION_{mode}.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8"
    )
    if not reproducible:
        print("FAIL: a builder changed supplied polynomial bytes", file=sys.stderr)
    print(f"Overall {result['status']}: {len(receipts)} finite verification phases.",
          flush=True)
    return 0 if success else 1


if __name__ == "__main__":
    raise SystemExit(main())
