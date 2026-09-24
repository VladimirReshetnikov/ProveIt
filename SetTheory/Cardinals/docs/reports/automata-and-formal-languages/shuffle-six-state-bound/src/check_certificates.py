#!/usr/bin/env python3
"""Check the finite shuffle predecessor certificates using only Python's stdlib.

This checks local witnesses, not exhaustive coverage. Run coverage.cpp as well.
All validation uses explicit exceptions (not Python assertions).
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
from typing import Any


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def is_int(x: Any) -> bool:
    return type(x) is int


def check_record(rec: dict[str, Any]) -> dict[str, int]:
    require(isinstance(rec, dict), "record must be an object")
    m, n, family = rec.get("m"), rec.get("n"), rec.get("family")
    require(is_int(m) and 2 <= m <= 6, "m outside 2..6")
    require(is_int(n) and n >= 2, "n must be at least two")
    require(is_int(family) and family >= 0, "bad family mask")
    columns = rec.get("columns")
    require(isinstance(columns, list) and len(columns) == n, "bad columns length")
    require(all(is_int(s) and 0 < s < (1 << m) - 1 for s in columns),
            "columns must be nonempty proper subsets")
    require(columns == sorted(set(columns)), "columns not strictly increasing")
    require(family == sum(1 << s for s in columns), "family encoding mismatch")
    for j, a in enumerate(columns):
        require(a.bit_count() >= 2, "a column has degree below two")
        for k, b in enumerate(columns):
            require(j == k or (a & b) != a, "comparable columns")
    rows = [{j for j, s in enumerate(columns) if s & (1 << i)} for i in range(m)]
    for i, a in enumerate(rows):
        require(len(a) >= 2, "a row has degree below two")
        for k, b in enumerate(rows):
            require(i == k or not a <= b, "comparable rows")
    require(rec.get("status") == "sat", "record has no positive witness")
    f, g, raw_T = rec.get("f"), rec.get("g"), rec.get("T")
    require(isinstance(f, list) and len(f) == m, "bad f length")
    require(isinstance(g, list) and len(g) == n, "bad g length")
    require(all(is_int(x) and 0 <= x < m for x in f), "f out of range")
    require(all(is_int(x) and 0 <= x < n for x in g), "g out of range")
    require(isinstance(raw_T, list), "T is not a list")
    for pair in raw_T:
        require(isinstance(pair, list) and len(pair) == 2, "bad cell")
        i, j = pair
        require(is_int(i) and is_int(j) and 0 <= i < m and 0 <= j < n,
                "cell out of range")
    T = {tuple(pair) for pair in raw_T}
    require(len(T) == len(raw_T), "duplicate cell in T")
    S = {(i, j) for i in range(m) for j in rows[i]}
    require(len(T) < len(S), "predecessor is not strictly smaller")
    require({i for i, j in T} == set(range(m)), "predecessor misses a row")
    require({j for i, j in T} == set(range(n)), "predecessor misses a column")
    actual_image = {(f[i], j) for i, j in T} | {(i, g[j]) for i, j in T}
    require(actual_image == S, "transition image does not equal target")
    return {"m": m, "n": n, "target_size": len(S), "predecessor_size": len(T)}


def check_file(path: Path, targets_out: Path | None = None) -> dict[str, Any]:
    counts: Counter[tuple[int, int]] = Counter()
    by_m: Counter[int] = Counter()
    size_pairs: Counter[tuple[int, int]] = Counter()
    seen: set[tuple[int, int]] = set()
    records = []
    for line_number, line in enumerate(path.read_text().splitlines(), 1):
        require(bool(line.strip()), f"blank line {line_number}")
        try:
            rec = json.loads(line)
            stats = check_record(rec)
            key = (rec["m"], rec["family"])
            require(key not in seen, "duplicate target record")
            seen.add(key)
        except (ValueError, KeyError, TypeError) as exc:
            raise ValueError(f"{path.name}: line {line_number}: {exc}") from exc
        counts[(stats["m"], stats["n"])] += 1
        by_m[stats["m"]] += 1
        size_pairs[(stats["target_size"], stats["predecessor_size"])] += 1
        records.append(rec)
    require(bool(records), "empty certificate file")
    if targets_out is not None:
        targets_out.parent.mkdir(parents=True, exist_ok=True)
        targets_out.write_text("".join(f"{m}\t{family}\n" for m, family in sorted(seen)))
    return {
        "result": "PASS: all local certificates valid; coverage must be checked separately",
        "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "records": len(records),
        "by_rows": {str(m): by_m[m] for m in range(2, 7)},
        "by_shape": {f"{m}x{n}": count for (m, n), count in sorted(counts.items())},
        "target_size_range": [min(s for s, t in size_pairs), max(s for s, t in size_pairs)],
        "predecessor_size_range": [min(t for s, t in size_pairs), max(t for s, t in size_pairs)],
        "decrease_range": [min(s-t for s,t in size_pairs), max(s-t for s,t in size_pairs)]
    }


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificates", type=Path, nargs="?", default=root / "data/certificates.jsonl")
    parser.add_argument("--targets-out", type=Path, default=root / "audit/verified_targets.tsv")
    parser.add_argument("--report", type=Path, default=root / "audit/local_check.json")
    args = parser.parse_args()
    try:
        result = check_file(args.certificates, args.targets_out)
        args.report.parent.mkdir(parents=True, exist_ok=True)
        args.report.write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(result, indent=2))
    except (OSError, ValueError) as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
