#!/usr/bin/env python3
"""Rebuild the finite certificates for finite-cover phase repair.

Python standard library only. All certificate arithmetic is exact. This is
an independently runnable computational check, not a Lean/kernel proof.
Run ``python3 verify_exact.py`` to compare with the shipped certificates;
run ``python3 verify_exact.py --write`` to regenerate them.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction
from itertools import product
from math import comb, factorial, isqrt, prod
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def compositions(total: int, parts: int):
    if parts == 1:
        yield (total,)
    else:
        for a in range(total + 1):
            for rest in compositions(total - a, parts - 1):
                yield (a,) + rest


def ternary_certificate() -> dict:
    """Accumulate all 9^5 cubes in Z[zeta_3][z_0^+-1,...,z_8^+-1]."""
    points = tuple(product(range(3), repeat=2))
    bits = tuple(product(range(2), repeat=4))
    counts: dict[tuple[int, ...], list[int]] = defaultdict(lambda: [0, 0, 0])
    cube_count = 0
    for hs in product(points, repeat=4):
        phase = -sum(hs[j][1] * prod(hs[k][0] for k in range(4) if k != j)
                     for j in range(4)) % 3
        shifts = [(sum(b[j] * hs[j][0] for j in range(4)) % 3,
                   sum(b[j] * hs[j][1] for j in range(4)) % 3,
                   (-1) ** sum(b)) for b in bits]
        for x, y in points:
            powers = [0] * 9
            for sx, sy, sign in shifts:
                powers[3 * ((x + sx) % 3) + ((y + sy) % 3)] += sign
            counts[tuple(powers)][phase] += 1
            cube_count += 1
    require(cube_count == 3**10, "Incorrect number of cubes")
    records = []
    groups: dict[tuple[int, ...], dict] = {}
    triangle_numerator = 0
    cancelled_cube_count = 0
    constant = None
    all_at_one = [0, 0]
    for powers, raw in sorted(counts.items()):
        # zeta^2 = -1-zeta; the reduced pair means a+b*zeta.
        a, b = raw[0] - raw[2], raw[1] - raw[2]
        if a == b == 0:
            cancelled_cube_count += sum(raw)
            continue
        norm_squared = a*a - a*b + b*b
        absolute_value = isqrt(norm_squared)
        require(absolute_value**2 == norm_squared,
                "A coefficient has a nonintegral absolute value")
        require(sum(powers) == 0, "Global phase invariance failed")
        triangle_numerator += absolute_value
        all_at_one[0] += a
        all_at_one[1] += b
        signature = tuple(sorted(powers))
        if signature not in groups:
            groups[signature] = {"signature": list(signature), "monomials": 0,
                                 "coefficient_absolute_value": absolute_value}
        require(groups[signature]["coefficient_absolute_value"] == absolute_value,
                "Signature class has varying coefficient magnitude")
        groups[signature]["monomials"] += 1
        records.append({"powers": list(powers), "raw_root_counts": raw,
                        "coefficient": [a, b], "absolute_value": absolute_value})
        if not any(powers):
            constant = [a, b]
    require(len(records) == 289, "Wrong number of retained monomials")
    require(constant == [20457, 0], "Wrong constant coefficient")
    require(cancelled_cube_count == 20736, "Wrong cancelled cube count")
    require(triangle_numerator == 29673, "Wrong triangle numerator")
    require(all_at_one == [24057, 0], "Wrong constant-function energy")
    require(Fraction(triangle_numerator, cube_count) == Fraction(1099, 2187),
            "Wrong upper bound")
    require(Fraction(all_at_one[0], cube_count) == Fraction(11, 27),
            "Wrong lower bound")
    return {
        "description": "Exact ternary quartic Laurent certificate; coefficient=[a,b] means a+b*zeta_3",
        "point_order": [list(v) for v in points],
        "cube_count": cube_count,
        "exponents_before_cancellation": len(counts),
        "retained_monomials": len(records),
        "cancelled_cube_count": cancelled_cube_count,
        "constant_coefficient": constant,
        "triangle_numerator": triangle_numerator,
        "upper_bound": str(Fraction(triangle_numerator, cube_count)),
        "constant_function_energy": str(Fraction(all_at_one[0], cube_count)),
        "signature_classes": [groups[s] for s in sorted(groups)],
        "monomials": records,
    }


def multi_difference(table: dict[tuple[int, ...], Fraction], moduli: tuple[int, ...],
                     orders: tuple[int, ...], base: tuple[int, ...]) -> Fraction:
    out = Fraction(0)
    for shifts in product(*(range(a + 1) for a in orders)):
        coefficient = (-1)**(sum(orders) - sum(shifts))
        coefficient *= prod(comb(a, b) for a, b in zip(orders, shifts))
        point = tuple((x + y) % m for x, y, m in zip(base, shifts, moduli))
        out += coefficient * table[point]
    return out % 1


def verify_primitive(moduli: tuple[int, ...], degree: int, function,
                     expected_top: dict[tuple[int, ...], Fraction]) -> int:
    points = tuple(product(*(range(m) for m in moduli)))
    table = {x: Fraction(function(x)) % 1 for x in points}
    checks = 0
    for total in (degree, degree + 1):
        for orders in compositions(total, len(moduli)):
            target = expected_top.get(orders, Fraction(0)) % 1 if total == degree else Fraction(0)
            for base in points:
                actual = multi_difference(table, moduli, orders, base)
                require(actual == target,
                        f"Difference mismatch: {moduli=}, {degree=}, {orders=}, {base=}, {actual=}, {target=}")
                checks += 1
    return checks


def primitive_regressions() -> dict:
    cases = []
    # Odd-prime explicit primitive bases in dimension two.
    for p in (3, 5, 7):
        d = p + 1
        for orders in compositions(d, 2):
            if all(m < p for m in orders):
                case_checks = verify_primitive(
                    (p, p), d,
                    lambda x, orders=orders, p=p: Fraction(prod(comb(t, m) for t, m in zip(x, orders)), p),
                    {orders: Fraction(1, p)})
                cases.append({"kind": "classical_binomial", "p": p,
                              "orders": list(orders), "checks": case_checks})
        for i in range(2):
            orders = tuple(d if j == i else 0 for j in range(2))
            case_checks = verify_primitive(
                (p, p), d,
                lambda x, i=i, p=p: -Fraction(comb(x[i], 2), p*p),
                {orders: Fraction(1, p)})
            cases.append({"kind": "odd_diagonal", "p": p, "coordinate": i,
                          "checks": case_checks})
        case_checks = verify_primitive(
            (p, p), d, lambda x, p=p: -Fraction(x[0]*x[1], p*p),
            {(p, 1): Fraction(1, p), (1, p): Fraction(1, p)})
        cases.append({"kind": "odd_transfer_pair", "p": p, "checks": case_checks})
    # Boolean cubic basis in dimension three, including depth two.
    for i in range(3):
        orders = tuple(3 if j == i else 0 for j in range(3))
        checks = verify_primitive((2, 2, 2), 3, lambda x, i=i: Fraction(x[i], 8),
                                  {orders: Fraction(1, 2)})
        cases.append({"kind": "boolean_diagonal", "coordinate": i, "checks": checks})
    for i in range(3):
        for j in range(i+1, 3):
            m1 = tuple(2 if k == i else 1 if k == j else 0 for k in range(3))
            m2 = tuple(1 if k == i else 2 if k == j else 0 for k in range(3))
            checks = verify_primitive((2, 2, 2), 3,
                                      lambda x, i=i, j=j: Fraction(x[i]*x[j], 4),
                                      {m1: Fraction(1, 2), m2: Fraction(1, 2)})
            cases.append({"kind": "boolean_transfer_pair", "coordinates": [i,j], "checks": checks})
    checks = verify_primitive((2, 2, 2), 3, lambda x: Fraction(prod(x), 2),
                              {(1, 1, 1): Fraction(1, 2)})
    cases.append({"kind": "boolean_squarefree", "checks": checks})
    # Optimal one-block covers, including all basepoints.
    for p in (2, 3, 5, 7):
        checks = verify_primitive((p*p, p), p+1,
                                  lambda x, p=p: Fraction(comb(x[0], p)*x[1], p),
                                  {(p, 1): Fraction(1, p)})
        cases.append({"kind": "minimal_one_block_cover", "p": p, "checks": checks})
    # Uniform field covers: every symmetric tensor coefficient separately.
    for p, d, q in ((2, 3, 4), (3, 4, 9)):
        for orders in compositions(d, 2):
            checks = verify_primitive((q, q), d,
                                      lambda x, p=p, orders=orders:
                                      Fraction(prod(comb(t, m) for t, m in zip(x, orders)), p),
                                      {orders: Fraction(1, p)})
            cases.append({"kind": "uniform_field_cover", "p": p, "degree": d,
                          "orders": list(orders), "checks": checks})
    checks = verify_primitive((24,), 3, lambda x: Fraction(x[0]**3, 24),
                              {(3,): Fraction(1, 4)})
    cases.append({"kind": "composite_group_cover", "checks": checks})
    return {"cases": cases, "number_of_cases": len(cases),
            "generator_difference_checks": sum(c["checks"] for c in cases),
            "scope": "Exact finite regression checks, not a proof for arbitrary prime or dimension"}


def selected_energy_regression() -> dict:
    points = tuple(product(range(2), repeat=2))
    f = dict(zip(points, (Fraction(0), Fraction(1,2), Fraction(-1), Fraction(3,4))))
    def add(a, b):
        return tuple((x+y) % 2 for x,y in zip(a,b))
    def derivative_value(base, hs):
        # f is real; conjugation is the identity, so every factor multiplies.
        ans = Fraction(1)
        for bits in product(range(2), repeat=len(hs)):
            v = base
            for bit, h in zip(bits, hs):
                if bit:
                    v = add(v,h)
            ans *= f[v]
        return ans
    def tensor(hs):
        return sum(hs[j][1] * prod(hs[k][0] for k in range(3) if k != j)
                   for j in range(3)) % 2
    cube = sum(derivative_value(x, hs) * (-1)**tensor(hs)
               for hs in product(points, repeat=3) for x in points) / 4**4
    selected = Fraction(0)
    for h1,h2 in product(points, repeat=2):
        fourier = sum(derivative_value(x, (h1,h2)) * (-1)**tensor((h1,h2,x))
                      for x in points) / 4
        selected += fourier**2 / 16
    require(cube == selected, "Selected Fourier-square identity failed")
    # H is the y-axis, where the canonical tensor vanishes.
    local = Fraction(0)
    for xcoordinate in range(2):
        local += sum(derivative_value((xcoordinate, y), hs)
                     for y in range(2)
                     for hs in product(((0,0),(0,1)), repeat=3)) / 32
    require(cube <= local, "Subgroup inequality regression failed")
    return {"cube_energy": str(cube), "selected_energy": str(selected),
            "mean_restricted_energy": str(local),
            "includes_zeros_and_nonunit_amplitudes": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate, rather than compare, JSON files")
    args = parser.parse_args()
    certificate = ternary_certificate()
    regressions = primitive_regressions()
    selected = selected_energy_regression()
    report = {"status": "passed", "arithmetic": "integers and fractions only",
              "ternary_cubes": certificate["cube_count"],
              "retained_monomials": certificate["retained_monomials"],
              "upper_bound": certificate["upper_bound"],
              "lower_bound": certificate["constant_function_energy"],
              "primitive_regressions": regressions,
              "selected_energy_regression": selected,
              "formal_proof_assistant_verification": False}
    for name, data in (("ternary_quartic_certificate.json", certificate),
                       ("verification_report.json", report)):
        path = ROOT / "data" / name
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        else:
            require(path.exists(), f"Missing certificate: {path}; use --write to generate")
            require(json.loads(path.read_text(encoding="utf-8")) == data,
                    f"Certificate mismatch: {path}")
    print(f"PASS: {certificate['cube_count']} ternary cubes; {certificate['retained_monomials']} monomials")
    print(f"PASS: upper {certificate['upper_bound']}; lower {certificate['constant_function_energy']}")
    print(f"PASS: {regressions['number_of_cases']} primitive cases; "
          f"{regressions['generator_difference_checks']} exact difference checks")
    print("PASS: selected-energy and subgroup regressions, including zero amplitudes")
    print("This is an exact computational certificate, not a proof-assistant build.")


if __name__ == "__main__":
    main()
