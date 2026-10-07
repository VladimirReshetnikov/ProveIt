#!/usr/bin/env python3
"""Exact finite diagnostics for the characteristic-three rigidity theorem.

The mathematical proofs are in sections/rigidity.tex.  These checks use
independent integer energy counts; they are not a proof for arbitrary groups.
Only the Python standard library is required.  No assertions are used.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def finite_group(moduli):
    elems = list(product(*(range(m) for m in moduli)))
    index = {x: i for i, x in enumerate(elems)}
    add = [[index[tuple((a + b) % m for a, b, m in zip(x, y, moduli))]
            for y in elems] for x in elems]
    neg = [index[tuple((-a) % m for a, m in zip(x, moduli))] for x in elems]
    sub = [[add[x][neg[y]] for y in range(len(elems))] for x in range(len(elems))]
    return elems, add, neg, sub


def rank3(vectors):
    mat = [list(v) for v in vectors]
    row = 0
    for col in range(len(mat[0])):
        pivot = next((i for i in range(row, len(mat)) if mat[i][col]), None)
        if pivot is None:
            continue
        mat[row], mat[pivot] = mat[pivot], mat[row]
        inv = 1 if mat[row][col] == 1 else 2
        mat[row] = [(v * inv) % 3 for v in mat[row]]
        for i in range(len(mat)):
            if i != row:
                q = mat[i][col]
                mat[i] = [(v - q * w) % 3 for v, w in zip(mat[i], mat[row])]
        row += 1
        if row == len(mat):
            break
    return row


def table_check():
    elems, add, neg, sub = finite_group((3, 3, 3))
    forms = elems
    cases = Counter()
    for ui, vi, wi in product(range(1, 27), repeat=3):
        u, v, w = elems[ui], elems[vi], elems[wi]
        rs = rank3((u, v, w))
        unequal = (ui != vi) + (ui != wi) + (vi != wi)
        opposite = (ui == neg[vi]) + (ui == neg[wi]) + (vi == neg[wi])
        schur = (add[ui][vi] == wi) + (add[ui][wi] == vi) + (add[vi][wi] == ui)
        # 3*kappa is 0, 3, or 2.  Thus K=9 E kappa is sum/9.
        accumulator = 0
        for ell in forms:
            vals = [sum(a * b for a, b in zip(ell, z)) % 3 for z in (u, v, w)]
            if all(vals):
                accumulator += 3 if vals[0] == vals[1] == vals[2] else 2
        kernel = Fraction(accumulator, 9)
        upper = 6 - Fraction(2 * unequal - opposite + 4 * schur, 3)
        if rs >= 2:
            upper -= Fraction(4, 3)
        require(kernel <= upper, (u, v, w, kernel, upper))
        cases[(rs, unequal, opposite, schur, str(kernel))] += 1
    require(len(cases) == 7, cases)
    return [{"rank": k[0], "unequal_pairs": k[1], "opposite_pairs": k[2],
             "schur_equations": k[3], "kernel": k[4], "triples": count}
            for k, count in sorted(cases.items())]


def pointwise_check():
    count = 0
    for s in range(1, 31):
        for m in range(s // 2 + 1):
            for b, c in product(range(m + 1), repeat=2):
                for a in range(s - b - c + 1):
                    r = a + b + c
                    left = r * (s - r) + a * (b + c) + 3 * b * c
                    require(left >= (s - m) * (b + c), (s, m, a, b, c))
                    count += 1
    return count


def graph_energy(f, domain, target):
    add_g = domain[1]
    sub_w = target[3]
    return sum(sum(v * v for v in Counter(sub_w[f[add_g[h][x]]][f[x]]
                                          for x in range(len(f))).values())
               for h in range(len(f)))


def signed_energy(f, domain, target):
    add_g, add_w = domain[1], target[1]
    points = [i for i, v in enumerate(f) if v]
    conv = Counter()
    for i in points:
        for j in points:
            z = add_g[i][j]
            a, b = f[i], f[j]
            conv[z, add_w[a][b]] += 1
            conv[z, a] -= 1
            conv[z, b] -= 1
            conv[z, 0] += 1
    return sum(v * v for v in conv.values())


def statistics(f, target):
    elems, add, neg, sub = target
    colors = Counter(f)
    colors.pop(0, None)
    s = sum(colors.values())
    M = sum(v * v for v in colors.values())
    A = s * s - M
    C = sum(v * colors.get(neg[u], 0) for u, v in colors.items())
    Z = sum(cu * cv * colors.get(add[u][v], 0)
            for u, cu in colors.items() for v, cv in colors.items())
    # T=s^3 - sum of cubes of the masses of projective target lines.
    lines = Counter()
    for u, cu in colors.items():
        lines[min(u, neg[u])] += cu
    T = s ** 3 - sum(v ** 3 for v in lines.values())
    return s, M, A, C, Z, T


def affine_maps(domain, target):
    elems_g, add_g, neg_g, sub_g = domain
    elems_w, add_w, neg_w, sub_w = target
    dims = len(elems_g[0])
    moduli = [max(x[i] for x in elems_g) + 1 for i in range(dims)]
    candidates = [range(len(elems_w)) if m % 3 == 0 else [0] for m in moduli]
    maps = []
    for images in product(*candidates):
        linear = []
        for x in elems_g:
            val = 0
            for count, image in zip(x, images):
                for _ in range(count % 3):
                    val = add_w[val][image]
            linear.append(val)
        for offset in range(len(elems_w)):
            maps.append(tuple(add_w[v][offset] for v in linear))
    return maps


def check_map(f, domain, target, affine, threshold):
    N = len(f)
    E = graph_energy(f, domain, target)
    ED = signed_energy(f, domain, target)
    s, M, A, C, Z, T = statistics(f, target)
    profile = 4 * s * N * N - 10 * s * s * N + 6 * s ** 3
    gap = N ** 3 - E - profile
    require(3 * gap >= 3 * (2 * N - 3 * s) * (2 * A - C) + 4 * T,
            ("master", f, E, s, A, C, T))
    require(3 * ED <= 18 * s ** 3 - 6 * s * A + 3 * s * C - 12 * Z - 4 * T,
            ("signed", f, ED, s, A, C, Z, T))
    identity = N ** 3 - 4 * s * N * N + N * (6 * s * s + 4 * M + 2 * C)
    identity += -4 * s ** 3 - 8 * s * M - 4 * s * C + 4 * Z + ED
    require(identity == E, ("expansion", f, E, identity))
    if 0 < 3 * s < 2 * N:
        require(gap >= 0, ("cubic", f))
        if gap == 0:
            require(A == 0, ("equality colors", f))
            S = [i for i, v in enumerate(f) if v]
            r = Counter(domain[3][x][y] for x in S for y in S)
            require(sum(v * v for v in r.values()) == s ** 3, ("equality coset", f))
    scalar = len(target[0]) == 3
    if scalar:
        x, y = f.count(1), f.count(2)
        require(ED <= 6 * s ** 3 - 12 * x * y * max(x, y), ("two-color", f))
        require(gap >= (2 * N - 6 * min(x, y)) * 2 * x * y,
                ("scalar imbalance", f))
    qualifies = Fraction(N ** 3 - E, N ** 3) < threshold
    if qualifies:
        distances = [sum(a != b for a, b in zip(f, ell)) for ell in affine]
        d = min(distances)
        require(distances.count(d) == 1, ("unique recovery", f, distances))
        require(3 * d < N and 9 * d * d - 12 * d * N + 2 * N * N > 0,
                ("inverse branch", f, d))
        require(N ** 3 - E >= 4 * d * N * N - 10 * d * d * N + 6 * d ** 3,
                ("inverse cubic", f, d))
    return int(qualifies), int(gap == 0 and 0 < 3 * s < 2 * N)


def exhaustive_family(moduli_g, dimension_w):
    domain = finite_group(moduli_g)
    target = finite_group((3,) * dimension_w)
    affine = affine_maps(domain, target)
    threshold = Fraction(4, 9) if all(m == 3 for m in moduli_g) else Fraction(1, 4)
    count = recovered = equalities = 0
    for f in product(range(len(target[0])), repeat=len(domain[0])):
        rc, eq = check_map(f, domain, target, affine, threshold)
        count += 1
        recovered += rc
        equalities += eq
    return {"domain_moduli": list(moduli_g), "target_dimension": dimension_w,
            "maps": count, "recovery_threshold": str(threshold),
            "maps_inside_recovery_range": recovered, "positive_local_equalities": equalities}


def structured_checks():
    results = []
    for N in (12, 13, 14, 16, 27, 31, 81):
        domain = finite_group((N,))
        target = finite_group((3, 3))
        affine = affine_maps(domain, target)
        maps = []
        for s in range(min(N, 6) + 1):
            for palette in ((1,), (1, 2), (1, 3, 4)):
                f = [0] * N
                for j in range(s):
                    f[j] = palette[j % len(palette)]
                maps.append(tuple(f))
        for f in maps:
            check_map(f, domain, target, affine, Fraction(1, 4))
        results.append({"cyclic_order": N, "maps": len(maps)})
    domain = finite_group((3, 3, 3))
    target = finite_group((3, 3))
    affine = affine_maps(domain, target)
    count = 0
    for s in range(9):
        for palette in ((1,), (1, 2), (1, 3, 4)):
            f = [0] * 27
            for j in range(s):
                f[j] = palette[j % len(palette)]
            check_map(tuple(f), domain, target, affine, Fraction(4, 9))
            count += 1
    results.append({"domain_moduli": [3, 3, 3], "maps": count})
    endpoints = []
    for modulus, f in ((2, (0, 1)), (3, (0, 0, 1))):
        domain, target = finite_group((modulus,)), finite_group((3,))
        energy = graph_energy(f, domain, target)
        ds = [sum(a != b for a, b in zip(f, ell)) for ell in affine_maps(domain, target)]
        endpoints.append({"order": modulus, "graph_energy": energy,
                          "defect": str(Fraction(modulus ** 3 - energy, modulus ** 3)),
                          "nearest_distance": str(Fraction(min(ds), modulus)),
                          "nearest_affine_maps": ds.count(min(ds))})
    require(endpoints[0]["defect"] == "1/4" and endpoints[0]["nearest_affine_maps"] == 2,
            endpoints)
    require(endpoints[1]["defect"] == "4/9" and endpoints[1]["nearest_affine_maps"] == 3,
            endpoints)
    return results, endpoints


def main():
    report = {"arithmetic": "exact Python integers and fractions", "assertions_used": False}
    report["pointwise_integer_cases"] = pointwise_check()
    report["projection_table"] = table_check()
    families = []
    for N in range(2, 10):
        families.append(exhaustive_family((N,), 1))
    families.append(exhaustive_family((3, 3), 1))
    for N in range(2, 6):
        families.append(exhaustive_family((N,), 2))
    report["exhaustive_families"] = families
    report["exhaustive_maps"] = sum(x["maps"] for x in families)
    report["structured_families"], report["sharp_recovery_endpoints"] = structured_checks()
    report["status"] = "all checks passed"
    path = Path(__file__).resolve().parents[1] / "data" / "rigidity_checks.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "exhaustive_maps": report["exhaustive_maps"],
                      "report": str(path)}, indent=2))


if __name__ == "__main__":
    main()
