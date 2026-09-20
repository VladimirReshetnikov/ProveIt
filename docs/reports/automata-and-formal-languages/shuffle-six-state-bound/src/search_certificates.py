#!/usr/bin/env python3
"""Optional regeneration of witnesses; the two checkers do not require Z3."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time
from check_certificates import check_record
from solver_engine import getpred


def main():
    root = Path(__file__).resolve().parents[1]
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--targets", type=Path, default=root / "audit/enumerated_targets.tsv")
    p.add_argument("--output", type=Path, default=root / "audit/regenerated_certificates.jsonl")
    p.add_argument("--timeout", type=int, default=2000, help="first attempt, milliseconds")
    p.add_argument("--retry-timeout", type=int, default=10000)
    p.add_argument("--limit", type=int, default=None, help="smoke-test only the first N targets")
    args = p.parse_args()
    targets = [tuple(map(int, line.split())) for line in args.targets.read_text().splitlines()]
    if args.limit is not None:
        targets = targets[:args.limit]
    if args.output.exists():
        raise FileExistsError(f"refusing to overwrite {args.output}; choose a new output path")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    start = time.perf_counter()
    with args.output.open("x") as out:
        for k, (m, family) in enumerate(targets, 1):
            columns = [s for s in range(1, (1 << m)-1) if family & (1 << s)]
            n = len(columns)
            S = {(i, j) for i in range(m) for j, s in enumerate(columns) if s & (1 << i)}
            witness = getpred(S, m, n, timeout=args.timeout, spanning=True)
            if witness["status"] == "unknown":
                witness = getpred(S, m, n, timeout=args.retry_timeout, spanning=True)
            record = {"m":m, "n":n, "family":family, "columns":columns, **witness}
            if record["status"] != "sat":
                raise RuntimeError(f"no witness found for {(m, family)}: {witness}")
            # Convert tuples to the on-disk JSON cell representation for checking.
            record = json.loads(json.dumps(record))
            check_record(record)
            out.write(json.dumps(record) + "\n")
            if k % 200 == 0:
                out.flush()
                print(f"{k}/{len(targets)} valid certificates; {time.perf_counter()-start:.2f}s", flush=True)
    print(f"PASS: {len(targets)} certificates in {time.perf_counter()-start:.2f}s")

if __name__ == "__main__":
    main()
