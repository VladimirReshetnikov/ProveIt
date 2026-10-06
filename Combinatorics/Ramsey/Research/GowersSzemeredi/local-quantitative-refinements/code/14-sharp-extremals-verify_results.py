#!/usr/bin/env python3
"""Independent finite diagnostics for Gowers extremal refinements.

The proofs are in the article. These checks use exact integer arithmetic
for combinatorial identities and explicitly labelled floating-point
arithmetic for Fourier inequalities. Requires Python 3 and NumPy.
"""
from collections import Counter
from decimal import Decimal, getcontext
from fractions import Fraction
from itertools import product
from pathlib import Path
import json
import numpy as np

ROOT = Path(__file__).resolve().parent


def sparse_cube_identity():
    vertices = list(product((0, 1), repeat=3))
    rows = Counter()
    checked = 0
    for frequencies in product(range(-2, 3), repeat=8):
        checked += 1
        if sum(frequencies):
            continue
        if any(sum(r * vertex[j] for r, vertex in zip(frequencies, vertices))
               for j in range(3)):
            continue
        rows[(frequencies.count(0),
              sum(abs(r) == 1 for r in frequencies),
              sum(abs(r) == 2 for r in frequencies))] += 1
    expected = {(8, 0, 0): 1, (4, 4, 0): 24, (4, 0, 4): 24,
                (3, 4, 1): 16, (2, 4, 2): 96,
                (0, 8, 0): 8, (0, 4, 4): 48, (0, 0, 8): 8}
    assert dict(rows) == expected
    return {"assignments_checked": checked,
            "surviving_assignments": sum(rows.values()),
            "exact_rows": [{"powers": list(k), "count": v,
                            "coefficient": str(Fraction(v, 2 ** (k[1] + k[2])))}
                           for k, v in sorted(rows.items(), reverse=True)]}


def fourier_checks():
    rng = np.random.default_rng(20261006)
    results = []
    maximum_identity_error = 0.0
    minimum_gap_margin = float("inf")
    cases = 0
    for n in (5, 7, 11, 13, 17, 25):
        r = np.arange(n)
        for sample in range(24):
            a = np.zeros(n, dtype=complex)
            for j in range(1, (n + 1) // 2):
                a[j] = (rng.normal() + 1j * rng.normal()) / n
                a[-j] = a[j].conjugate()
            if sample % 2 == 0:
                # Concentrated spectra stress the asymptotic argument.
                a *= 10 ** (-sample / 12)
                dominant = 5 if n == 25 else 1
                a[dominant] = .4 + .1j
                a[-dominant] = .4 - .1j
            f = (np.fft.ifft(a) * n).real
            T = np.empty((n, n), dtype=complex)
            for s in range(n):
                for t in range(n):
                    T[s, t] = np.sum(a * a[(r+s) % n].conj()
                                      * a[(r+t) % n].conj() * a[(r+s+t) % n])
            U8 = float(np.sum(abs(T) ** 2))
            direct = 0.0
            for h1 in range(n):
                for h2 in range(n):
                    for h3 in range(n):
                        v = np.ones(n)
                        for e1, e2, e3 in product((0, 1), repeat=3):
                            v *= f[(r+e1*h1+e2*h2+e3*h3) % n]
                        direct += float(v.sum())
            direct /= n ** 4
            error = abs(direct - U8) / max(1, U8)
            assert error < 2e-11, (n, sample, error)
            maximum_identity_error = max(maximum_identity_error, error)
            xi = int(np.argmax(abs(a)))
            rho = abs(a[xi])
            mask = np.ones(n, dtype=bool)
            mask[[xi, (-xi) % n]] = False
            D = float(np.sum(abs(a[mask]) ** 4))
            S = float(np.sum(abs(a) ** 4))
            b = abs(a[(2*xi) % n])
            axes_bound = 2*S*S + 12*rho**4*D
            refined_bound = (axes_bound + 8*rho**4*b**4
                             - 16*rho**3*D**1.25 - 16*rho**2*D**1.5)
            assert U8 + 1e-12 >= axes_bound
            assert U8 + 1e-12 >= refined_bound
            slots = {(sx*xi % n, sy*3*xi % n)
                     for sx in (-1, 1) for sy in (-1, 1)}
            slots |= {(t, s) for s, t in list(slots)}
            assert len(slots) == 8 and all(s and t for s, t in slots)
            bound = 2*rho*(D/2)**.75 + D
            for s, t in slots:
                assert abs(T[s, t] - rho*rho*b*b) <= bound + 1e-12
            minimum_gap_margin = min(minimum_gap_margin, U8 - 2*S*S)
            cases += 1
        results.append(n)
    return {"cyclic_group_orders": results, "cases": cases,
            "maximum_relative_identity_error": maximum_identity_error,
            "minimum_norm_gap_margin": minimum_gap_margin,
            "tolerance": "2e-11 for Fourier identity; 1e-12 for inequalities"}


def energy_checks():
    checked = equality = 0
    for n in range(1, 11):
        cosets = set()
        for step in range(1, n+1):
            if n % step == 0:
                for c in range(step):
                    cosets.add(frozenset(range(c, n, step)))
        for mask in range(1, 1 << n):
            A = frozenset(j for j in range(n) if mask >> j & 1)
            m = len(A)
            r = Counter((a-b) % n for a in A for b in A)
            E = sum(v*v for v in r.values())
            assert E <= m**3
            assert (E == m**3) == (A in cosets)
            equality += E == m**3
            checked += 1
    sharp = []
    for q in (101, 103, 127, 211, 1009):
        m = q-1
        E = m*m + m*(m-1)**2
        epsilon = 1 - Fraction(E, m**3)
        distance = Fraction(1, m)
        assert epsilon == distance * (1-distance)
        assert epsilon <= Fraction(1, 100)
        sharp.append({"q": q, "size": m, "energy": E,
                      "epsilon": str(epsilon), "distance_ratio": str(distance)})
    # Integer verification of the defect-polynomial factorization.
    defect_cases = 0
    for denominator in range(1, 121):
        for dt in range(denominator//3 + 1):
            delta = Fraction(dt, denominator)
            for tx in range(dt+1):
                x = Fraction(tx, denominator)
                raw = ((delta-x)*(1-x)*(1-delta)
                       + 3*x*(1-x)*(1-2*x))
                correction = x*(2+delta*delta-(8+delta)*x+6*x*x)
                assert raw - delta*(1-delta) == correction >= 0
                defect_cases += 1
    return {"all_nonempty_subsets_checked": checked,
            "exact_coset_equalities": equality, "sharp_examples": sharp,
            "rational_defect_checks": defect_cases}


def arrangement_checks():
    p = 3
    points = list(product(range(p), repeat=2))
    index = {v: i for i, v in enumerate(points)}
    cubes = []
    for h in points:
        entries = []
        for y in points:
            entries.append([index[((y[0]+e[0]*h[0]) % p,
                                   (y[1]+e[1]*h[1]) % p)]
                            for e in product((0, 1), repeat=2)])
        cubes.append(entries)
    masks = [[sum(1 << j for j in set(c)) for c in entries] for entries in cubes]
    rectangular = set()
    coordinate_cosets = [{x} for x in range(p)] + [set(range(p))]
    for A in coordinate_cosets:
        for B in coordinate_cosets:
            rectangular.add(frozenset(index[(a, b)] for a in A for b in B))
    equalities = 0
    for mask in range(1, 1 << 9):
        A = frozenset(i for i in range(9) if mask >> i & 1)
        Q = sum(sum((c & mask) == c for c in entries)**2 for entries in masks)
        assert Q <= len(A)**3
        assert (Q == len(A)**3) == (A in rectangular)
        equalities += Q == len(A)**3
    # Every labeling of the full 3x3 rectangle: exact equality classification.
    labels = np.array(list(product(range(p), repeat=9)), dtype=np.int16)
    good = np.ones(len(labels), dtype=bool)
    signs = np.array([1, -1, -1, 1])
    for entries in cubes:
        values = (labels[:, np.array(entries)] @ signs) % p
        good &= np.all(values == values[:, :1], axis=1)
    count = int(good.sum())
    assert count == p**6
    model_labels = set()
    for c in range(p):
        for one in product(range(p), repeat=p):
            for two_tail in product(range(p), repeat=p-1):
                two = (0,) + two_tail
                model_labels.add(tuple((c*x*y+one[x]+two[y]) % p for x,y in points))
    actual = {tuple(row) for row in labels[good]}
    assert actual == model_labels
    return {"domains_checked": 511, "rectangular_coset_equalities": equalities,
            "full_rectangle_labelings_checked": len(labels),
            "exact_multiaffine_plus_lower_order_labelings": count}


def norm3(x, y, z, p=5):
    # Determinant of multiplication by x+y*T+z*T^2 in F5[T]/(T^3+T+1).
    # Columns come from products with 1, T, T^2; the cubic has no F5 root.
    a,b,c = x, -z, -y
    d,e,f = y, x-z, -y-z
    g,h,i = z, y, x-z
    return (a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)) % p


def coloring_checks():
    p = 5
    assert all((x**3+x+1) % p for x in range(p))
    points3 = np.array(list(product(range(p), repeat=3)), dtype=np.int16)
    norms = np.array([norm3(*v) for v in points3])
    assert np.count_nonzero(norms == 0) == 1
    points = np.array(list(product(range(p), repeat=4)), dtype=np.int16)
    def colors(v):
        return np.array([norm3(*x[:3])+x[3] for x in v], dtype=np.int16) % p
    minima = len(points)
    maximum = 0
    # A four-term AP is symmetric iff its colors agree at parameters +/-1,+/-3.
    for center in points:
        first = colors((center+points) % p) == colors((center-points) % p)
        second = colors((center+3*points) % p) == colors((center-3*points) % p)
        directions = int(np.count_nonzero(first & second))
        assert directions == 1
        minima = min(minima, directions)
        maximum = max(maximum, directions)
    # The quadratic x+y^2 has a center-dependent 1-dimensional direction kernel.
    directions2 = np.array(list(product(range(p), repeat=2)))
    for x, y in product(range(p), repeat=2):
        good = [tuple(h) for h in directions2 if (h[0]+2*y*h[1]) % p == 0]
        assert len(good) == p
    return {"field": "F_5", "irreducible_polynomial": "T^3+T+1",
            "norm_form_inputs": len(points3), "centers": len(points),
            "directions_per_center_checked": len(points),
            "minimum_including_zero": minima, "maximum_including_zero": maximum,
            "free_coordinate_direction_counts": {str(d): p**(d-4) for d in (4,5,6,7)},
            "nontrivial_ordered_AP_minima": {str(d): p**d*(p**(d-4)-1) for d in (4,5,6,7)}}


def asymptotic_values():
    getcontext().prec = 90
    two = Decimal(2)
    sqrt2 = two.sqrt()
    c = (sqrt2/6) ** (Decimal(1)/3)
    target = (Decimal(9)/4) ** (Decimal(1)/3)
    delta = Decimal("0.25")
    out = []
    for exponent in range(1, 10):
        u = Decimal(10) ** (-exponent)
        b = c * delta ** (-Decimal(1)/3) * u ** (Decimal(4)/3)
        a4 = -3*b**4 + (32*u**8 + 8*b**8).sqrt()
        assert a4 > 0
        norm_power = (a4*a4+6*a4*b**4+b**8)/32
        assert abs(norm_power/u**8-1) < Decimal("1e-75")
        excess = (Decimal("1.5")*delta**4*(a4+b**4)
                  + Decimal(".5")*delta**3*a4*b
                  + Decimal("1.5")*delta**2*a4*b*b + norm_power)
        residual = ((excess - 6*sqrt2*delta**4*u**4)
                    / (delta ** (Decimal(8)/3) * u ** (Decimal(16)/3)))
        out.append({"u": str(u), "normalized_secondary_correction": str(residual),
                    "limiting_constant": str(target)})
    assert abs(Decimal(out[-1]["normalized_secondary_correction"])-target) < Decimal("0.0001")
    return out


def main():
    results = {"role": "finite diagnostics supplementing the written proofs",
               "seed": 20261006,
               "sparse_cube_identity": sparse_cube_identity(),
               "fourier_checks": fourier_checks(),
               "energy_checks": energy_checks(),
               "arrangement_checks": arrangement_checks(),
               "coloring_checks": coloring_checks(),
               "asymptotic_values": asymptotic_values()}
    (ROOT / "verification_results.json").write_text(json.dumps(results, indent=2)+"\n")
    print(json.dumps({"status": "PASS", "sections": list(results)[2:],
                      "output": "verification_results.json"}))


if __name__ == "__main__":
    main()
