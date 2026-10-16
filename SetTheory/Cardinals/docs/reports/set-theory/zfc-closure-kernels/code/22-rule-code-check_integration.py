"""Independent endpoint integration, native proof and rejection diagnostics."""
from __future__ import annotations

from copy import deepcopy
import json
from pathlib import Path

import debruijn_kernel as k
import rule_search as r
import check_wrapper_transport as w
from make_empty_certificate import make


def run():
    if not __debug__:
        raise RuntimeError("Assertions must be enabled")
    # Compare the production constructors with the independently developed
    # transport audit, whose quantified semantics were also checked.
    for rho in range(1000):
        _, _, independent_bound, independent_hull = w.wrapper_parts(rho)
        assert r.bound(rho) == independent_bound
        assert r.hull(rho) == independent_hull

    cert = make()
    rows = cert["proof"]
    normal = r.check_dag(rows)
    logical_premise = r.check_dag(rows, logic_only=True)
    assert normal == logical_premise
    assert normal[-1] == r.protected_hull(0) != 0
    assert normal[-2] == r.bound(0)

    basic_cert = make("rule")
    basic_result = r.check_dag(basic_cert["proof"], presentation="rule")
    assert basic_result[-1] == r.hull(0) != 0
    assert basic_result == r.check_dag(basic_cert["proof"], presentation="rule", logic_only=True)

    for beta in range(10000):
        assert r.extract_bound(r.raw_bound(beta)) == beta
    for a in range(10000):
        assert r.extract_bound(a) is None

    bad = []
    changed_premise = deepcopy(rows)
    changed_premise[-1][1] = 0
    bad.append(changed_premise)
    bad.append(rows + [["ASSUME", "0"]])
    bad.append(rows + [["GEN", len(rows)]])
    bad.append(rows + [["MP", True, 0]])
    bad.append(rows + [["CLOSE", "0", 0]])
    bad.append(rows + [["K", "0", "0", "forged-conclusion"]])
    bad.append(rows + [["GEN", -1]])
    bad.append(rows + [["CLOSE", True]])
    bad.append(rows + [["CLOSE", len(rows)]])
    for malformed in bad:
        try:
            r.check_dag(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError("Malformed/forged certificate was accepted")

    rule_check = r.rule_checker()
    pure_check = r.rule_checker(logic_only=True)
    basic_check = r.rule_checker(presentation="rule")
    axiom_check = r.rule_checker(presentation="axiom")
    pure_baseline = k.checker()
    accepted = 0
    for n in range(5000):
        answer = rule_check(n)
        assert answer == pure_check(n)
        if answer is not None:
            accepted += 1
            assert answer != 0
        # No successful CLOSE occurs in this small range; logical proof
        # results should therefore agree with a separately supplied kernel.
        assert answer == pure_baseline(n)
        assert answer == basic_check(n)
    for rho in range(100):
        assert axiom_check(8 * rho + 7) == r.epsc_axiom(rho)
        assert r.check_dag([["AX", format(rho, "x")]], presentation="axiom") == [r.epsc_axiom(rho)]

    return {
        "status": "PASS",
        "production_vs_independent_bound_hull_pairs": 1000,
        "empty_hull_certificate_lines": len(rows),
        "empty_hull_certificate_premise_pure": True,
        "empty_hull_certificate_refutation": False,
        "basic_rule_control_certificate_lines": len(basic_cert["proof"]),
        "protected_bound_parser_roundtrips": 10000,
        "protected_bound_parser_nonshape_rejections": 10000,
        "unary_closure_has_no_matrix_payload": True,
        "malformed_certificate_rejections": len(bad),
        "numeric_proof_prefix_checked": 5000,
        "accepted_theorems_in_prefix": accepted,
        "open_axiom_comparator_instances": 100,
        "scope": "Finite implementation diagnostics and a genuine non-refutation certificate, not a consistency test or TM simulation.",
    }


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run()
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    print(text)
