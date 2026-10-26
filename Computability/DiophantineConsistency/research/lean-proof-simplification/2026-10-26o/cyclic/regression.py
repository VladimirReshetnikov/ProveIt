#!/usr/bin/env python3
"""Read-only arithmetic regressions by default; NOT Lean typechecking or proofs."""
import argparse
from itertools import product
from pathlib import Path
import json
import re
import hashlib

PIN = "b310142330df89e48413c8fce62e7de223e1c7d5"
BASELINE_SHA256 = {
    "CurrentCellCycle2011.lean": "874a68dc11255170f19dc1a5345e195f36379711f8af630b16dd6eb9fe77081d",
    "CurrentSouthShift2011.lean": "256403c28ff13e2fb8585597a1931c1be8703f6726daaf3c5509cfbff5f8cf8d",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def word(xs):
    return sum((1 << j) * x for j, x in enumerate(xs))


def signatures(text):
    # Textual comparison only, not a Lean parser. A multiset allows theorem reordering.
    starts = list(re.finditer(
        r'^(?:(?:@\[[^\n]*\]|private|noncomputable)\s+)*(?:theorem|def|abbrev|instance)\b',
        text, re.M))
    return sorted(text[m.start():text.index(':=', m.start())].strip()
                  for m in starts if ':=' in text[m.start():])


def run_checks(root):
    results = {"not_a_lean_proof": True, "pin": PIN}
    counts = {}
    for k in (1, 2):
        count = 0
        for south in product((0, 1), repeat=9):
            for prefix in product((0, 1), repeat=k):
                expected = word(prefix + south[:9-k])
                actual = ((1 << k) * word(south)) % 512 + word(prefix)
                require(expected == actual, f"Prefix identity failed: k={k}, south={south}, prefix={prefix}")
                count += 1
        counts[f"offset_{18+k}"] = count
    require(word((1, 1)) == 3, "Excluded two-bit prefix must have weight 3")
    require(all(word(p) <= 2 for p in ((0, 0), (1, 0), (0, 1))),
            "An admitted one-hot prefix exceeds the error bound")
    results['binary_prefix'] = {
        "tests": counts,
        "coverage": "Every 9-bit South word and every Boolean 1- or 2-bit prepended prefix; dropped high South bits independently varied.",
        "one_hot_error_boundary": "00,10,01 satisfy weighted error<=2; 11 gives 3 and must be excluded."}
    count = 0
    for N in range(1, 33):
        modulus = N * 2011
        for ai in range(N):
            for bi in range(N):
                a, b = ai * 2011, bi * 2011
                whole_shift = a - a % 2011
                difference = (b - whole_shift) % modulus
                j = difference // 2011
                require(difference % 2011 == 0 and j < N,
                        f"Difference witness is not a bounded aligned cell: N={N}, a={a}, b={b}")
                require((a + j * 2011) % modulus == b,
                        f"Difference witness misses target: N={N}, a={a}, b={b}")
                count += 1
    results['cyclic_witness'] = {
        "tests": count,
        "coverage": "All pairs of aligned cells for every N in 1..32, including the singleton cycle; validates the exact theta difference witness, not only existence."}
    checks = []
    for name, expected_hash in BASELINE_SHA256.items():
        before_bytes = (root / 'source' / name).read_bytes()
        after_bytes = (root / 'candidates' / name).read_bytes()
        before, after = before_bytes.decode(), after_bytes.decode()
        before_hash = hashlib.sha256(before_bytes).hexdigest()
        require(before_hash == expected_hash, f"Source snapshot does not match pinned baseline {PIN}: {name}")
        require(signatures(before) == signatures(after), f"Declaration signature changed: {name}")
        require(not re.search(r'\b(sorry|admit|axiom)\b', after), f"Unproved or axiomatic candidate: {name}")
        checks.append({
            "file": name,
            "signatures_unchanged": True,
            "before_lines": len(before.splitlines()),
            "after_lines": len(after.splitlines()),
            "before_nonblank_lines": sum(bool(x.strip()) for x in before.splitlines()),
            "after_nonblank_lines": sum(bool(x.strip()) for x in after.splitlines()),
            "sha256_before": before_hash,
            "sha256_after": hashlib.sha256(after_bytes).hexdigest()})
    results['static_source_checks'] = checks
    results['lean_compilation'] = 'NOT RUN: Lean compiler was not run.'
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
                        help='Explicitly write JSON to this path; otherwise only print to stdout.')
    args = parser.parse_args()
    report = json.dumps(run_checks(Path(__file__).resolve().parent), indent=2) + '\n'
    if args.output is not None:
        args.output.write_text(report)
    print(report, end='')


if __name__ == '__main__':
    main()
