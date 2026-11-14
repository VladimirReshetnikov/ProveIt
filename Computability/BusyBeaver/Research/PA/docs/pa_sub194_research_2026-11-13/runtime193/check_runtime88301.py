#!/usr/bin/env python3
"""Freshly verify all primary-source contracts for the 193-control core.

The inherited arithmetic oracles are hypotheses. The changed skip-zero oracle
is transported by the explicit next-bit-one two-transition identity. This is
ordinary symbolic verification, not a newly compiled Lean theorem. It does not
establish a calibrated blank startup. Defaults are read-only.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packet", type=Path, nargs="?", default=HERE.parent / "reference/haz")
    parser.add_argument("--out", type=Path, help="Optional fresh artifact directory")
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit("Run Python without -O.")
    sys.path.insert(0, str(args.packet / "vendor"))
    import compiler as c
    original = args.packet / "inputs/pa194.native.tm"
    assert hashlib.sha256(original.read_bytes()).hexdigest() == "e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54"
    rows = {}
    for line in original.read_text().splitlines():
        q, b, w, direction, target = line.split()
        rows[int(q), int(b)] = int(w), direction == "R", int(target)
    old = dict(rows)
    rows[88, 0], rows[51, 0] = (0, False, 51), (0, True, 122)
    rows = {key: (w, direction, 88 if target == 301 else target)
            for key, (w, direction, target) in rows.items() if key[0] != 301}
    assert old[16, 1] == rows[122, 1] == (0, False, 1)
    sites, instructions, contracts = c.source(c.read_grammar(args.packet / "inputs/pa194.grammar.json"))
    result = c.validate(rows, contracts)
    assert result == dict(ok=True, contracts=4780, max_steps=497, total_steps=1479852)
    text = "".join(f"{q} {b} {w} {'R' if direction else 'L'} {target}\n"
                   for (q, b), (w, direction, target) in sorted(rows.items()))
    digest = hashlib.sha256(text.encode()).hexdigest()
    assert digest == "50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53"
    assert text.encode() == (HERE / "runtime193.native.tm").read_bytes()
    assert [["".join(map(str, path)), op, arg] for path, op, arg in sites] == json.loads((HERE / "primary.sites.json").read_text())
    assert [list(code) for code in instructions] == json.loads((HERE / "primary.instructions.json").read_text())
    result.update(working_states=193, source_sites=len(sites), table_sha256=digest,
        max_source_path_length=max(len(path) for path, _, _ in sites),
        oracle_scope="Gap n is any Nat; physical file is any finite Nat list of length at least10. First9 fields are work registers, the rest nonempty spares. Zero/positive branch assumption as appropriate. Blank exterior.",
        marker_lemma="At skip51's unmarked block delimiter, the following bit is1. Old16/1 and new122/1 are both0L1; the two-step endpoints agree.",
        source_context_collector_used=False, kernel_checked=False,
        blank_start_status="Rejected; separate literal all-start certificates.")
    if args.out:
        args.out.mkdir(parents=True, exist_ok=True)
        (args.out / "runtime_verification.json").write_text(json.dumps(result, indent=2) + "\n")
        (args.out / "runtime193.native.tm").write_text(text)
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
