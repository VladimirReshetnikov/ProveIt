#!/usr/bin/env python3
"""Check the finite part of the fourth-parameter range obstruction.

The HC model and its soundness for the other native rows are mathematical
dependencies, not conclusions of this finite checker. Run without -O.
"""

import argparse
import itertools
import json
from pathlib import Path

if not __debug__:
    raise RuntimeError("Assertions must be enabled")

# Source 140's implication algebra, used with its full HC interpretation.
IMP = ((3, 3, 3, 3), (3, 3, 1, 3), (3, 3, 3, 3), (0, 0, 0, 3))
VALUES = range(4)


def implication(a, b):
    return IMP[a][b]


def lukasiewicz(a, b, c, u):
    return implication(
        implication(implication(c, u), a),
        implication(implication(a, c), implication(b, c)),
    )


def pair(a, b):
    return (a + b) * (a + b + 1) // 2 + b


def code(tag, a, b):
    return 4 * pair(a, b) + tag


def formula_code(a, b, c, u):
    imp = lambda x, y: code(0, x, y)
    return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)

    failures = [
        dict(A=a, B=b, C=c, U=u, value=lukasiewicz(a, b, c, u))
        for a, b, c, u in itertools.product(VALUES, repeat=4)
        if lukasiewicz(a, b, c, u) != 3
    ]
    assert failures == [
        dict(A=0, B=3, C=1, U=2, value=0),
        dict(A=1, B=3, C=1, U=2, value=0),
    ]
    implication_range = sorted({implication(a, b) for a, b in itertools.product(VALUES, repeat=2)})
    assert implication_range == [0, 1, 3]
    safe_checks = 0
    for a, b, c in itertools.product(VALUES, repeat=3):
        # Includes all possible I/Q/E results, as well as the three inputs.
        for u in (0, 1, 3, a, b, c):
            assert lukasiewicz(a, b, c, u) == 3
            safe_checks += 1

    # The open R(A,B) proposal has an actual native instance outside this
    # obstruction. In HC choose p != q, k with e(q)(k)=0, e(p)(k)=1, and
    # z in the uncountable fiber of k outside p union q union {p,q}.
    # Assignment: label0=p, label1=label2=z, label3=q.
    # Then A=R(0,0) has value0, B=code0 has value3, C=R(2,3) has
    # value1, and U=R(codeA,codeB)=R(1,0) has value2.
    a, b, c = 1, 0, code(1, 2, 3)
    u = code(1, a, b)
    assert (a, b, c, u) == (1, 0, 73, 5)
    assert lukasiewicz(0, 3, 1, 2) == 0
    for x, y in itertools.product(VALUES, repeat=2):
        assert not (x == 3 and implication(x, y) == 3) or y == 3

    result = dict(
        status="FINITE_RANGE_OBSTRUCTION_PASS",
        implication_table=IMP,
        designated_value=3,
        falsum_value=0,
        unrestricted_instances=256,
        unrestricted_failures=failures,
        implication_range=implication_range,
        quantifier_and_equality_ranges="{0,3}, by the inherited HC semantics",
        safe_choice_checks=safe_checks,
        safe_choice_set="{0,1,3,A,B,C}",
        mp_checks=16,
        excluded_family="Every total native U-builder returning code0, code1, A, B, C, or an I/Q/E-headed code, pointwise on its inputs",
        membership_proposal_counterexample=dict(
            builder="U=R(A,B), treating input formula codes as variable labels",
            codes=dict(A=a, B=b, C=c, U=u, instance=str(formula_code(a, b, c, u))),
            values=dict(A=0, B=3, C=1, U=2, instance=0),
            assignment="0=p, 1=z, 2=z, 3=q; r(z,q)=1 and r(z,p)=2",
            interpretation="The inherited HC model does NOT validate this proposed family",
        ),
        limitations=[
            "No finite check establishes the unbounded HC model or proof induction",
            "R(A,B) has no consistency-strength calibration here",
            "No new machine, source compiler, runtime certificate, or Lean endpoint",
        ],
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "safe_choice_checks": safe_checks,
                      "unrestricted_failures": failures}, sort_keys=True))


if __name__ == "__main__":
    main()
