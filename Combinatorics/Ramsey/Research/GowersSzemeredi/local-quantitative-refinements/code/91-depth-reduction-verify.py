"""Reproducible exact checks and floating-point diagnostics for the article.

Exact: Laurent-exponent identities; modular cyclic degree; multivariate
coordinate-difference vanishing; symbolic cyclotomic extension degrees.
Numerical: exhaustive finite root-phase optimizations; spectral identities;
weighted selection. Numerical checks are not proofs of real inequalities.
"""
from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
import random
from collections import Counter
from pathlib import Path

from depth_reduction import (atoms, cyclic_scores, digit_phase, inner,
                             reduce_samples, transfer_constant)


def difference(values: list[int], modulus: int) -> list[int]:
    return [(values[(i + 1) % len(values)] - values[i]) % modulus
            for i in range(len(values))]


def cyclic_degree(values: list[int], modulus: int, cap: int) -> int:
    current = [x % modulus for x in values]
    for order in range(1, cap + 2):
        current = difference(current, modulus)
        if not any(current):
            return order - 1
    raise AssertionError("degree cap exceeded")


def compositions(total: int, n: int):
    if n == 1:
        yield (total,)
    else:
        for k in range(total + 1):
            for tail in compositions(total - k, n - 1):
                yield (k,) + tail


def coordinate_difference(values, points, index, p, axis, modulus):
    out = []
    for k, x in enumerate(points):
        y = list(x)
        y[axis] = (y[axis] + 1) % p
        out.append((values[index[tuple(y)]] - values[k]) % modulus)
    return out


def check_degree(values, points, p, degree, modulus):
    index = {x: i for i, x in enumerate(points)}
    for orders in compositions(degree + 1, len(points[0])):
        current = values[:]
        for axis, order in enumerate(orders):
            for _ in range(order):
                current = coordinate_difference(current, points, index,
                                                p, axis, modulus)
        if any(current):
            return False
    return True


def run(output: Path):
    rng = random.Random(20261007)
    report = {"seed": 20261007, "status": "passed", "exact": {},
              "numerical": {}, "warning": "No Lean verification; floating-point diagnostics are not proofs."}
    params = [(p, a) for p in (2, 3, 5, 7, 11) for a in (1, 2, 3)]

    # The pointwise atomic decomposition is an identity of Laurent monomials.
    exponent_cases = 0
    for p, a in params:
        for t in range(p):
            left = Counter(t - s for s in range(p))
            right = Counter(j - p * int(t < j) for j in range(p))
            assert left == right
            exponent_cases += 1
    report["exact"]["laurent_exponent_cases"] = exponent_cases

    degree_rows = []
    for p, a in params:
        d = 1 + a * (p - 1)
        digit_deg = cyclic_degree(list(range(p)), p**(a + 1), d)
        assert digit_deg == d
        step_degrees = [cyclic_degree([int(t < j) for t in range(p)],
                                      p**a, d - 1) for j in range(p)]
        assert max(step_degrees) <= d - 1
        degree_rows.append({"p": p, "a": a, "digit_degree": digit_deg,
                            "step_degrees": step_degrees})
    report["exact"]["cyclic_degrees"] = degree_rows

    mv_rows = []
    for p, a, n in ((2, 1, 3), (2, 2, 3), (2, 3, 3),
                     (3, 1, 2), (3, 2, 2), (5, 1, 2)):
        points = list(itertools.product(range(p), repeat=n))
        M, m = p**(a + 1), p**a
        d = 1 + a * (p - 1)
        for trial in range(8):
            coeff = [rng.randrange(p) for _ in range(n)]
            if not any(coeff):
                coeff[0] = 1
            # A critical-depth digit sum plus a classical monomial.
            exponents = [0] * n
            remaining = d
            for axis in range(n):
                exponents[axis] = min(p - 1, remaining)
                remaining -= exponents[axis]
            cc = rng.randrange(p)
            values = []
            for x in points:
                mon = math.prod(x[i]**exponents[i] for i in range(n))
                values.append((sum(c*t for c, t in zip(coeff, x))
                               + cc * (M // p) * mon) % M)
            assert check_degree(values, points, p, d, M)
            residues = [r % p for r in values]
            assert residues == [sum(c*t for c, t in zip(coeff, x)) % p
                                 for x in points]
            for j in range(p):
                reduced = [(r // p - int(r % p < j)) % m for r in values]
                assert check_degree(reduced, points, p, d, m)
        mv_rows.append({"p": p, "a": a, "dimension": n,
                        "polynomials": 8, "candidates_each": p})
    report["exact"]["multivariate_degree_checks"] = mv_rows

    # Optional symbolic verification of the elementary cyclotomic field degrees.
    try:
        import sympy as sp
        x = sp.Symbol("x")
        field_rows = []
        for p, a in params:
            small = sp.Poly(sp.cyclotomic_poly(p**a, x), x)
            large = sp.Poly(sp.cyclotomic_poly(p**(a+1), x), x)
            assert large.degree() == p * small.degree()
            # Eisenstein certificate after translation x -> x+1.
            shifted = sp.Poly(large.as_expr().subs(x, x+1).expand(), x)
            coeffs = shifted.all_coeffs()
            assert coeffs[0] == 1 and coeffs[-1] % p == 0
            assert coeffs[-1] % (p*p) != 0
            assert all(c % p == 0 for c in coeffs[1:])
            field_rows.append({"p": p, "a": a,
                               "degrees": [small.degree(), large.degree()]})
        report["exact"]["cyclotomic_eisenstein"] = field_rows
    except ImportError:
        report["exact"]["cyclotomic_eisenstein"] = "skipped: sympy not installed"

    max_identity_error = max_frame_error = max_score_error = 0.0
    max_transfer_violation = max_stability_violation = 0.0
    random_cases = 0
    for p, a in params:
        m, M = p**a, p**(a+1)
        zeta = cmath.exp(2j*math.pi/M)
        vp = digit_phase(p, a)
        aa = atoms(p, a)
        d0 = sum(z.conjugate() for z in vp)/p
        for t in range(p):
            rhs = sum(zeta**j * aa[j][t] for j in range(p))/(p*d0)
            max_identity_error = max(max_identity_error, abs(rhs-vp[t]))
        basis = [[vp[t]*cmath.exp(2j*math.pi*r*t/p) for t in range(p)]
                 for r in range(p)]
        dd = [inner([1+0j]*p, v) for v in basis]
        s2 = min(abs(x)**2 for x in dd[1:])
        c = transfer_constant(p, a)
        for _ in range(40):
            f = [complex(rng.uniform(-1,1), rng.uniform(-1,1)) for _ in range(p)]
            scores = cyclic_scores(f, p, a)
            direct = [inner(f, atom) for atom in aa]
            max_score_error = max(max_score_error, max(abs(u-v) for u,v in zip(scores,direct)))
            bb = [inner(f, v) for v in basis]
            lhs = sum(abs(z)**2 for z in scores)/p
            rhs = sum(abs(d)**2*abs(b)**2 for d,b in zip(dd,bb))
            max_frame_error = max(max_frame_error, abs(lhs-rhs))
            top = max(abs(z) for z in scores)
            max_transfer_violation = max(max_transfer_violation, c*abs(bb[0])-top)
            residual2 = sum(abs(z)**2 for z in f)/p-abs(bb[0])**2
            max_stability_violation = max(max_stability_violation,
                c*c*abs(bb[0])**2+s2*residual2-top*top)
            random_cases += 1
    assert max_identity_error < 1e-11
    assert max_frame_error < 1e-11 and max_score_error < 1e-11
    assert max_transfer_violation < 1e-11 and max_stability_violation < 1e-11
    report["numerical"]["random_cyclic"] = {
        "cases": random_cases, "max_atomic_identity_error": max_identity_error,
        "max_frame_error": max_frame_error, "max_prefix_score_error": max_score_error,
        "max_transfer_violation": max_transfer_violation,
        "max_stability_violation": max_stability_violation}

    weighted_cases = 0
    weighted_error = 0.0
    for p,a in params:
        M = p**(a+1)
        for _ in range(10):
            samples = [(rng.randrange(M), complex(rng.uniform(-1,1),rng.uniform(-1,1)),
                        rng.random() if rng.random()>.2 else 0.0) for _ in range(17)]
            result = reduce_samples(samples,p,a)
            direct = sum(w*z*cmath.exp(-2j*math.pi*result.phase_residue(r)/p**a)
                         for r,z,w in samples)/sum(w for _,_,w in samples)
            weighted_error = max(weighted_error,abs(direct-result.selected_correlation))
            assert abs(result.selected_correlation)+1e-11 >= result.theoretical_factor*abs(result.original_correlation)
            weighted_cases += 1
    assert weighted_error < 1e-11
    report["numerical"]["weighted_selection"] = {
        "cases": weighted_cases, "max_score_error": weighted_error,
        "note": "Arbitrary sample residues; verifies the pointwise transfer, not polynomiality."}

    # Exhaust all root-valued vectors modulo a common root rotation (a_0=1).
    enum_rows = []
    for p,a in ((2,1),(2,2),(2,3),(3,1),(3,2),(3,3),
                 (5,1),(5,2),(7,1)):
        m = p**a
        roots = [cmath.exp(2j*math.pi*q/m) for q in range(m)]
        v = digit_phase(p,a)
        c = transfer_constant(p,a)
        best = -1.0
        maximizing = 0
        count = 0
        expected = set()
        for atom in atoms(p,a):
            expected.add(tuple(round(cmath.phase(z/atom[0])*m/(2*math.pi))%m
                               for z in atom))
        observed = set()
        for tail in itertools.product(range(m), repeat=p-1):
            labels = (0,)+tail
            score = abs(sum(v[t]*roots[labels[t]].conjugate() for t in range(p))/p)
            best = max(best,score)
            if abs(score-c) < 1e-10:
                maximizing += 1
                observed.add(labels)
            assert score <= c + 1e-10
            count += 1
        assert maximizing == p and observed == expected
        enum_rows.append({"p": p, "a": a, "normalized_patterns": count,
                          "maximum": best, "theoretical": c,
                          "maximizers": maximizing, "tolerance": 1e-10})
    report["numerical"]["exhaustive_root_patterns"] = enum_rows
    report["numerical"]["exhaustive_pattern_total"] = sum(r["normalized_patterns"] for r in enum_rows)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,
                        default=Path(__file__).resolve().parents[1]/"data"/"verification.json")
    args = parser.parse_args()
    run(args.output)
