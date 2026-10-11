#!/usr/bin/env python3
"""Small exact S6 certificate audit; no numerical periods or matrix search.

Checks the frozen target normalization, the restricted separator, a
convergent single-by-double row that the zero extension does not annihilate,
and the convergence/counts of two proposed Cayley seeds.  This does not
verify S6: its vanishing remains the unsolved certificate target.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, product
from math import comb, gcd
from functools import reduce
import json
from pathlib import Path

PIN = "dcd95baeb7c0e914b138bddef6829c5b1d52b726"
# Integral omega letters: -1 encodes 0; j=0,1,2,3 encodes i**j.
ZERO = -1


def add(a, b, c=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + c * v
        if not out[k]:
            del out[k]
    return out


def word(z):
    ans, cumulative = [], 0
    for s, c in z:
        cumulative = (cumulative - c) % 4
        ans.extend([ZERO] * (s - 1) + [cumulative])
    return tuple(ans)


def indices(w):
    ans, s, previous = [], 1, 0
    for a in w:
        if a == ZERO:
            s += 1
        else:
            ans.append((s, (previous - a) % 4))
            previous, s = a, 1
    assert s == 1
    return tuple(ans)


def admissible(z):
    return bool(z) and z[0] != (1, 0)


def shuffle(u, v):
    # Direct interleaving enumeration, not the stuffle recursion.
    a, b = word(u), word(v)
    ans = Counter()
    for positions in combinations(range(len(a) + len(b)), len(a)):
        chosen = set(positions)
        ai = bi = 0
        out = []
        for j in range(len(a) + len(b)):
            if j in chosen:
                out.append(a[ai]); ai += 1
            else:
                out.append(b[bi]); bi += 1
        ans[indices(tuple(out))] += 1
    return dict(ans)


def stuffle(u, v):
    if not u:
        return {v: 1}
    if not v:
        return {u: 1}
    ans = {}
    for t, c in stuffle(u[1:], v).items():
        ans = add(ans, {(u[0],) + t: c})
    for t, c in stuffle(u, v[1:]).items():
        ans = add(ans, {(v[0],) + t: c})
    merged = (u[0][0] + v[0][0], (u[0][1] + v[0][1]) % 4)
    for t, c in stuffle(u[1:], v[1:]).items():
        ans = add(ans, {(merged,) + t: c})
    return ans


def ell(a, r, s):
    r, s = r % 4, s % 4
    if (r, s) == (1, 1):
        return (-1) ** (a + 1) * comb(5, a - 1)
    if (r, s) == (3, 3):
        return -(-1) ** (a + 1) * comb(5, a - 1)
    if a == 6 and (r, s) in ((1, 2), (3, 2)):
        return 1 if r == 1 else -1
    if a == 1 and (r, s) in ((2, 1), (2, 3)):
        return -1 if s == 1 else 1
    return 0


def ell_zero_extension(z):
    return ell(z[0][0], z[0][1], z[1][1]) if len(z) == 2 else 0


def cayley_omega(w):
    # The reverse pullback for phi(t)=(1-t)/(1+t), without (-1)**weight.
    image = {ZERO: 0, 0: ZERO, 1: 3, 2: None, 3: 1}
    out = {(): 1}
    for a in reversed(w):
        options = {2: -1}
        if image[a] is not None:
            options[image[a]] = 1
        out = {prefix + (b,): c * d
               for prefix, c in out.items() for b, d in options.items()}
    return out


def main():
    original = [485683200, -665395200, -36864000, 401080320,
                -258247, 11750400, 109347840, 971366400]
    # S6=K61+g61; beta(7)=61*pi**7/184320; Li_1(-1)=-log(2).
    converted = [Q(original[0]), Q(original[0] + original[1]),
                 Q(original[2]), Q(original[3]),
                 Q(original[4]) * Q(184320, 61),
                 Q(original[5]), Q(original[6]), -Q(original[7])]
    scale = Q(61, 46080)
    primitive = [642940, -237900, -48800, 530944,
                 -1032988, 15555, 144753, -1285880]
    assert [x * scale for x in converted] == primitive
    assert reduce(gcd, primitive) == 1

    row_checks = 0
    for p in range(1, 7):
        q = 7 - p
        for r, s in product(range(4), repeat=2):
            assert ell(p, r, s) + ell(q, s, r) == 0
            row_checks += 1
            val = sum(comb(q + j - 1, j) * ell(q + j, s, r - s)
                      for j in range(p))
            val += sum(comb(p + j - 1, j) * ell(p + j, r, s - r)
                       for j in range(q))
            assert val == 0
            row_checks += 1
    assert all(ell(a, 1, 0) == 0 for a in range(1, 7))

    u, v = ((1, 1),), ((5, 0), (1, 2))
    sh, st = shuffle(u, v), stuffle(u, v)
    expected_shuffle = {((a, 1), (6 - a, 3), (1, 2)): 1
                        for a in range(1, 6)}
    expected_shuffle.update({((5, 0), (1, 1), (1, 1)): 1,
                             ((5, 0), (1, 2), (1, 3)): 1})
    expected_stuffle = {
        ((1, 1), (5, 0), (1, 2)): 1,
        ((5, 0), (1, 1), (1, 2)): 1,
        ((5, 0), (1, 2), (1, 1)): 1,
        ((6, 1), (1, 2)): 1,
        ((5, 0), (2, 3)): 1,
    }
    assert sh == expected_shuffle
    assert st == expected_stuffle
    row = add(sh, st, -1)
    assert all(admissible(z) for z in row)
    assert all(sum(s for s, _ in z) == 7 for z in row)
    zero_extension_value = sum(c * ell_zero_extension(z) for z, c in row.items())
    assert zero_extension_value == -1

    # Im[Li5(1)Li2(-i)] = -G*zeta(5); its three stuffle terms have
    # imaginary parts U52, -g25, -beta(7), respectively.
    u_reduction = stuffle(((5, 0),), ((2, 3),))
    assert u_reduction == {((5, 0), (2, 3)): 1,
                           ((2, 3), (5, 0)): 1, ((7, 3),): 1}
    # K61 = Q7-g25-beta7+G*zeta5 in the primitive target.
    q_target = primitive.copy()
    q_target[3] -= primitive[0]
    q_target[4] -= primitive[0]
    q_target[5] += primitive[0]
    assert q_target == [642940, -237900, -48800, -111996,
                        -1675928, 658495, 144753, -1285880]

    seeds = {}
    for name, z in [("g_1_6", ((1, 1), (6, 0))),
                    ("g_6_1", ((6, 1), (1, 0)))]:
        w = word(z)
        transformed = cayley_omega(w)
        assert len(transformed) == 128
        assert all(a[0] != 0 and a[-1] != ZERO for a in transformed)
        assert all(len(a) == 7 for a in transformed)
        assert all(ZERO not in a for a in transformed)
        seeds[name] = {"indices_colors": z, "omega_word": w,
                       "transformed_terms": len(transformed),
                       "all_terms_convergent": True,
                       "all_transformed_terms_depth": 7}

    # Directly audit the p=6 specialization of the existing endpoint identity.
    endpoint_pi_coefficient = Q(61, 184320) + Q(5, 18432) + Q(7, 23040) + Q(31, 120960)
    assert endpoint_pi_coefficient == Q(4499, 3870720)

    receipt = {
        "result": "PASS",
        "scope": "Exact target and relation audit; NOT a proof of S6.",
        "source_commit": PIN,
        "arithmetic": "Python integers and fractions.Fraction; no numerical periods",
        "original_basket": ["S6", "g61", "g43", "g25", "pi^7", "G*zeta5", "beta4*zeta3", "beta6*log2"],
        "original_integer_vector": original,
        "primitive_word_target_basket": ["K61", "g61", "g43", "g25", "Im Li7(i)",
            "Im(Li2(i)Li5(1))", "Im(Li4(i)Li3(1))", "Im(Li6(i)Li1(-1))"],
        "primitive_word_target_vector": primitive,
        "scale_after_exact_substitution": str(scale),
        "primitive_gcd": 1,
        "restricted_rows_annihilated": row_checks,
        "separator_original_target": original[0],
        "separator_primitive_target": primitive[0],
        "single_by_double_row": {
            "u": u, "v": v, "shuffle_terms": len(sh), "stuffle_terms": len(st),
            "formal_row_terms": len(row), "all_terms_convergent": True,
            "zero_extended_separator_value": zero_extension_value,
            "row": [{"indices_colors": z, "coefficient": c} for z, c in sorted(row.items())]
        },
        "U52_single_product_reduction": "U52=g25+beta7-G*zeta5",
        "exact_S6_depth3_reduction": "S6=g61-g25+G*zeta5-beta7+Q7",
        "Q7_target_vector_in_same_product_conventions": q_target,
        "weight7_word_counts": {"convergent_raw": 16 * 5**5, "conjugation_fixed": 4 * 3**5,
                               "imaginary_coordinates": (16 * 5**5 - 4 * 3**5) // 2},
        "proposed_convergent_cayley_seeds": seeds,
        "p6_endpoint_pi_coefficient": str(endpoint_pi_coefficient),
        "remaining_exact_problem": "Find rational standard/Cayley rows whose sum is the primitive target; membership not computed."
    }
    out = (Path(__file__).resolve().parents[1] / "results" / "s6_target_audit.json")
    out.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: receipt[k] for k in ["result", "scope", "restricted_rows_annihilated",
                      "separator_primitive_target", "weight7_word_counts"]}, indent=2))
    print("single-by-double zero-extension diagnostic:", zero_extension_value)
    print("wrote", out)


if __name__ == "__main__":
    main()
