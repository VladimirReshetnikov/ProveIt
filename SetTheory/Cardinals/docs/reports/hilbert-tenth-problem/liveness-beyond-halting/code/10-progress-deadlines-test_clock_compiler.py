"""Finite exact checks. These tests do not prove infinite liveness or novelty."""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import platform
from clock_compiler import (Machine, Rule, StackOp, compile_trace, decode_stack,
                            encode_stack, example_machine, rational_stack)

COUNTS: Counter[str] = Counter()


def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(f"check failed: {category}")
    COUNTS[category] += 1


def test_stack_encodings() -> None:
    for length in range(9):
        for w in product((1, 3), repeat=length):
            n, x = encode_stack(w), rational_stack(w)
            check(decode_stack(n) == w, "integer_stack_roundtrips")
            check(Fraction(0) <= x < 1, "rational_range")
            for d in (1, 3):
                check(encode_stack((d,) + w) == 4*n+d, "integer_push")
                check(rational_stack((d,) + w) == (x+d)/4, "affine_push")
            if w:
                d, tail = w[0], w[1:]
                check(n == 4*encode_stack(tail)+d, "integer_pop")
                check(Fraction(d,4) <= x < Fraction(d+1,4), "top_interval")
                check(rational_stack(tail) == 4*x-d, "affine_pop")


def test_trace_certificates() -> None:
    m = example_machine()
    for H in range(6):
        ds = tuple(range(2, H+1, 3))
        cert = compile_trace(m, H, ds)
        check(len(cert.variables) == H*(3+len(m.rules)+m.G)+len(ds), "variable_formula")
        check(len(cert.residuals) == H*(4*len(m.rules)+m.E+2*m.G+2)+len(ds),
              "residual_formula")
        check(all(p.degree <= 2 for _, p in cert.residuals), "quadratic_degrees")
        quartic = cert.expanded_polynomial()
        check(quartic.degree <= 4, "quartic_degrees")
        for ids in product(range(len(m.rules)), repeat=H):
            run = m.run(ids)
            expected = run is not None and all(
                sum(c[0] in m.accepting for c in run[1:d+1]) >= j
                for j, d in enumerate(ds, 1))
            witness = cert.witness(ids)
            check((witness is not None) == expected, "trace_sequences")
            if witness is not None:
                check(cert.evaluate(witness) == 0, "valid_zero_certificates")
                check(quartic.evaluate(witness) == 0, "expanded_quartic_evaluation")
                for v in cert.variables:
                    altered = dict(witness)
                    altered[v] += 1
                    check(cert.evaluate(altered) > 0, "single_coordinate_mutations")
    # Impossible deadline: no target-accepting state at t=1.
    c = compile_trace(m, 1, (1,))
    for ids in product(range(len(m.rules)), repeat=1):
        check(c.witness(ids) is None, "impossible_deadline")


def test_exhaustive_local_auxiliaries() -> None:
    # One top-guarded stay transition (active remainder fixed at zero) and
    # one unguarded stay transition. Both are legal and observationally equal.
    # Rule-labelled witnesses must still be distinct; inactive u must be zero.
    m = Machine((Rule(0, 0, StackOp("top1", "stay")), Rule(0, 0)),
                (0, 5, 1), frozenset({0}))
    cert = compile_trace(m, 1, (1,))
    solutions = []
    # All zeros must have q'=0, x'=5, y'=1 by the active rule equations.
    # The following ranges deliberately include other configurations and
    # nonboolean selector choices, plus all feasible remainder candidates.
    domains = {
        "q_1": range(2), "x_1": range(8), "y_1": range(3),
        "e_0_0": range(3), "e_0_1": range(3),
        "u_0_0_x": range(3), "w_1": range(3),
    }
    for values in product(*(domains[v] for v in cert.variables)):
        assignment = dict(zip(cert.variables, values))
        if cert.evaluate(assignment) == 0:
            solutions.append(assignment)
        COUNTS["local_assignments_enumerated"] += 1
    expected = [cert.witness((0,)), cert.witness((1,))]
    check(len(solutions) == 2 and all(s in expected for s in solutions),
          "exhaustive_local_bijection")
    # With a zero-step trace, there are no witnesses and the polynomial is zero.
    zero = compile_trace(m, 0)
    check(zero.variables == () and zero.evaluate({}) == 0, "empty_horizon")


def burst_acceptance(N: int, t: int) -> int:
    # N unary continues, one stop, N accepting pulses, then rejecting sink.
    return max(0, min(N, t-(N+1)))


def test_deadline_coherence() -> None:
    for k in range(1, 13):
        check(burst_acceptance(k, 2*k+1) >= k, "incoherent_individual_feasibility")
    for k in range(2, 13):
        # To emit >=k pulses by 2k+1 necessarily N<=k. It suffices to test
        # N in 0..k, and none satisfies every earlier deadline.
        coherent = any(all(burst_acceptance(N, 2*j+1) >= j for j in range(1,k+1))
                       for N in range(k+1))
        check(not coherent, "coherent_prefix_obstruction")


def test_two_stack_guards() -> None:
    # Exercise empty and both top guards on both stacks, and all operations.
    words = [w for n in range(4) for w in product((1,3), repeat=n)]
    ops = [StackOp(g,u) for g in ("any","empty","top1","top3")
           for u in ("stay","push1","push3","pop")
           if u != "pop" or g.startswith("top")]
    for op in ops:
        for left in words:
            for right in words:
                m = Machine((Rule(0,1,op,op),),
                            (0,encode_stack(left),encode_stack(right)), frozenset({1}))
                c = compile_trace(m,1,(1,))
                w = c.witness((0,))
                legal = op.apply(m.initial[1]) is not None and op.apply(m.initial[2]) is not None
                check((w is not None) == legal, "two_stack_guard_cases")
                if w is not None:
                    check(c.evaluate(w) == 0, "two_stack_guard_zeros")


def test_invalid_inputs() -> None:
    for thunk in (lambda: StackOp("any","pop"),
                  lambda: decode_stack(0), lambda: decode_stack(6),
                  lambda: encode_stack((2,)),
                  lambda: compile_trace(example_machine(),2,(2,1)),
                  lambda: compile_trace(example_machine(),2,(3,)),
                  lambda: compile_trace(example_machine(),-1)):
        try:
            thunk()
        except ValueError:
            COUNTS["invalid_input_rejections"] += 1
        else:
            raise AssertionError("invalid input was accepted")


def main() -> None:
    for test in (test_stack_encodings, test_trace_certificates,
                 test_exhaustive_local_auxiliaries, test_deadline_coherence,
                 test_two_stack_guards, test_invalid_inputs):
        test()
    report = {
        "status": "PASS", "python": platform.python_version(),
        "integer_arithmetic": "exact; rational tests use fractions.Fraction",
        "scope": "finite checks, not a proof of infinite behavior or an MRDP extractor",
        "counts": dict(sorted(COUNTS.items())),
        "total_checks_and_enumerated_assignments": sum(COUNTS.values()),
    }
    out = Path(__file__).resolve().parents[1]/"artifacts"/"test_report.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    main()
