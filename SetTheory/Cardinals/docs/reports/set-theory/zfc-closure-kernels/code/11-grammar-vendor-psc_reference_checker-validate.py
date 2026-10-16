#!/usr/bin/env python3
"""Reproduce checker regressions and write a machine-readable evidence record.

The optional upstream comparison reads the independently pinned ProveIt file;
the checker and all ordinary tests themselves have no upstream dependency.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import platform
import sys
import unittest

import psc_checker as p
import test_psc_checker


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compare_upstream(path: Path) -> dict:
    spec = importlib.util.spec_from_file_location("pinned_kernel_metrics", path)
    upstream = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = upstream
    spec.loader.exec_module(upstream)
    a = p.Arena()
    matrices = (a.bottom, a.mem(0, 1), a.mem(5, 7),
                a.all(1, a.imp(a.mem(0, 1), a.mem(7, 2))),
                a.all(0, a.mem(0, 1)), a.neg(a.mem(0, 1)))

    def input_formula(formula):
        converted = []
        for node in a.nodes[:formula + 1]:
            if node[0] == p.BOT:
                out = upstream.Bot()
            elif node[0] == p.MEM:
                out = upstream.Mem(node[1], node[2])
            elif node[0] == p.IMP:
                out = upstream.Imp(converted[node[1]], converted[node[2]])
            else:
                out = upstream.All(node[1], converted[node[2]])
            converted.append(out)
        return converted[formula]

    def source_encode(formula):
        pending, pieces = [formula], []
        while pending:
            q = pending.pop()
            if q.op == "bot":
                pieces.append("00")
            elif q.op == "mem":
                pieces.extend(("01", p.unary(q.args[0]), p.unary(q.args[1])))
            elif q.op == "imp":
                pieces.append("10")
                pending.extend(reversed(q.args))
            elif q.op == "all":
                pieces.extend(("11", p.unary(q.args[0])))
                pending.append(q.args[1])
            else:
                raise AssertionError(f"unexpected source constructor {q.op}")
        return "".join(pieces)

    records = []
    for matrix in matrices:
        ours = p.encode_formula(a, a.psc(matrix))
        expected = source_encode(upstream.bottom_basis(
            upstream.seeded(input_formula(matrix), seed="subset", mixed=False)))
        if ours != expected:
            raise AssertionError("PSC generator differs from pinned source")
        records.append({"matrix_bits": p.encode_formula(a, matrix),
                        "generated_formula_bits": len(ours),
                        "exact_named_syntax_match": True})
    return {"source_sha256": sha256(path), "sample_count": len(records),
            "normalization": "none; source negation expanded as implication to Bottom",
            "samples": records}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream-kernel", type=Path)
    parser.add_argument("--output", type=Path, default=Path("validation.json"))
    args = parser.parse_args()
    suite = unittest.defaultTestLoader.loadTestsFromModule(test_psc_checker)
    stream = io.StringIO()
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(suite)
    if not result.wasSuccessful():
        print(stream.getvalue(), file=sys.stderr)
        return 1
    bits, original_arena, identity = p.identity_certificate()
    checked = p.check_derivation(bits)
    if p.encode_formula(checked.arena, checked.conclusion) != p.encode_formula(
            original_arena, identity):
        raise AssertionError("identity certificate conclusion mismatch")
    here = Path(__file__).resolve().parent
    identity_path = here / "identity.cert"
    if identity_path.exists() and identity_path.read_bytes() != bits.encode("ascii"):
        raise AssertionError("identity.cert bytes differ from canonical certificate")
    identity_path.write_bytes(bits.encode("ascii"))
    evidence = {
        "kind": "reference-checker-regression; not formal verification or consistency proof",
        "python": platform.python_version(),
        "tests_run": result.testsRun,
        "tests_successful": result.wasSuccessful(),
        "deep_binder_test_depth": 5000,
        "substitution_semantics_comparisons": 100 * 6 * 20,
        "identity": {"bits": len(bits), "lines": len(checked.lines),
                     "valid_derivation": True, "accepted_refutation": checked.is_refutation,
                     "conclusion": "Mem(0,1) -> Mem(0,1)",
                     "sha256": sha256(identity_path)},
        "bounded_census": p.enumerate_certificates(16),
        "file_sha256": {name: sha256(here / name) for name in
                        ("psc_checker.py", "test_psc_checker.py", "validate.py")},
        "unittest_log": stream.getvalue(),
    }
    if args.upstream_kernel:
        evidence["upstream_comparison"] = compare_upstream(args.upstream_kernel)
    args.output.write_text(json.dumps(evidence, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"output": str(args.output), "tests": result.testsRun,
                      "identity_bits": len(bits),
                      "bounded_census": evidence["bounded_census"],
                      "upstream_comparison": "upstream_comparison" in evidence}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
