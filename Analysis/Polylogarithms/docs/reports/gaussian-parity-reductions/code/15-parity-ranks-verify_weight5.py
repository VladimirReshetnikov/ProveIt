#!/usr/bin/env python3
"""Replay the proved weight-five shuffle relation and audit the open S4 formula.

Exact mode independently enumerates all labelled interleavings of the two
iterated-integral word pairs (1,4) and (2,3). It computes the imaginary
parts of the two classical products with SymPy and verifies the exact
combination 960*A-224*B. The original certificate is read for comparison
and is never overwritten.

Optional numerical mode computes the still-conjectural S4 formula from
independent integrals. Numerical agreement is explicitly not a proof.

    python code/verify_weight5.py
    python code/verify_weight5.py --numerical --dps 60

Dependencies: Python >=3.10, SymPy >=1.12; mpmath >=1.3 for --numerical.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations
import json
import math
from pathlib import Path
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
ELL, G, ZETA3, BETA4 = sp.symbols("ell G zeta3 beta4", real=True)
G14, G23, G32, G41 = sp.symbols("g14 g23 g32 g41", real=True)
DOUBLE_SYMBOLS = {"g14": G14, "g23": G23, "g32": G32, "g41": G41}
CONSTANT_MONOMIALS = {"pi^5": sp.pi**5, "G*zeta(3)": G*ZETA3,
                      "beta(4)*log(2)": BETA4*ELL}


def shuffle_words(p: int, q: int):
    """Enumerate labelled interleavings, preserving each input word's order."""
    left, right = (0,)*(p-1)+(1,), (0,)*(q-1)+(1,)
    counts = Counter()
    for left_positions in combinations(range(p+q), p):
        positions = set(left_positions)
        i = j = 0
        word = []
        for place in range(p+q):
            if place in positions:
                word.append(left[i])
                i += 1
            else:
                word.append(right[j])
                j += 1
        counts[tuple(word)] += 1
    assert sum(counts.values()) == math.comb(p+q, p)
    return counts


def word_indices(word):
    """Decode 0^(a-1)1 0^(b-1)1 as the descending indices (a,b)."""
    indices, zero_count = [], 0
    for letter in word:
        if letter == 0:
            zero_count += 1
        else:
            indices.append(zero_count+1)
            zero_count = 0
    assert zero_count == 0 and len(indices) == 2
    return tuple(indices)


def shuffle_row(p, q):
    coefficients = Counter()
    words = shuffle_words(p, q)
    for word, multiplicity in words.items():
        a, b = word_indices(word)
        coefficients[f"g{a}{b}"] += multiplicity
    return dict(sorted(coefficients.items())), words


def imaginary_single_product(p, q):
    """Exact classical values; independently transcribed from residue classes."""
    single = {
        1: -ELL/2+sp.I*sp.pi/4,
        2: -sp.pi**2/48+sp.I*G,
        3: -3*ZETA3/32+sp.I*sp.pi**3/32,
        4: -7*sp.pi**4/11520+sp.I*BETA4,
    }
    return sp.expand(sp.im(single[p]*single[q]))


def constant_coefficients(expression):
    expression = sp.expand(expression)
    row = {name: str(expression.coeff(monomial))
           for name, monomial in CONSTANT_MONOMIALS.items()}
    reconstructed = sum(sp.Rational(row[name])*monomial
                        for name, monomial in CONSTANT_MONOMIALS.items())
    assert sp.expand(expression-reconstructed) == 0
    return row


def exact_replay():
    rows, products, records = [], [], []
    for p, q in ((1, 4), (2, 3)):
        coefficients, words = shuffle_row(p, q)
        product = imaginary_single_product(p, q)
        rows.append(coefficients)
        products.append(product)
        records.append({"indices": [p, q],
                        "labelled_interleavings": sum(words.values()),
                        "words": {"".join(map(str, word)): count
                                  for word, count in sorted(words.items())},
                        "double_coefficients": coefficients,
                        "single_product_imaginary_part": constant_coefficients(product)})
    combined_double = sp.expand(sum(
        multiplier*sum(coefficient*DOUBLE_SYMBOLS[name]
                       for name, coefficient in row.items())
        for multiplier, row in zip((960, -224), rows)))
    target_double = 576*G41+288*G32+736*G23+960*G14
    assert sp.expand(combined_double-target_double) == 0
    combined_constant = sp.expand(960*products[0]-224*products[1])
    target_constant = 21*G*ZETA3-480*BETA4*ELL
    assert sp.expand(combined_constant-target_constant) == 0
    final_double = {name: int(combined_double.coeff(symbol))
                    for name, symbol in DOUBLE_SYMBOLS.items()}
    final_constant = constant_coefficients(combined_constant)
    payload = {"source_label": "gauss:eq:wt5-sporadic",
               "method": "Independent labelled-word interleaving enumeration and exact SymPy arithmetic",
               "first_shuffle": records[0], "second_shuffle": records[1],
               "certificate_multipliers": [960, -224],
               "final_double_coefficients": final_double,
               "final_constant_coefficients": final_constant,
               "pi_fifth_power_cancels_exactly": final_constant["pi^5"] == "0",
               "analytic_status": "Proved by the ordinary iterated-integral shuffle identity",
               "exact_replay_status": "pass"}
    original_path = ROOT/"results"/"weight5_shuffle_certificate.json"
    if original_path.exists():
        original = json.loads(original_path.read_text(encoding="utf-8"))
        for name in ("first_shuffle", "second_shuffle"):
            for key in ("indices", "double_coefficients", "single_product_imaginary_part"):
                assert payload[name][key] == original[name][key], (name, key)
        for key in ("certificate_multipliers", "final_double_coefficients",
                    "final_constant_coefficients", "pi_fifth_power_cancels_exactly"):
            assert payload[key] == original[key], key
        payload["original_certificate_comparison"] = "pass (10 exact field comparisons)"
    else:
        payload["original_certificate_comparison"] = "original file absent; independently generated certificate"
    return payload


def numerical_s4(dps):
    import mpmath as mp
    mp.mp.dps = dps
    cuts = [0, mp.mpf("0.1"), mp.mpf("0.5"), 1]
    def direct_double(a, b):
        z = 1j
        def integrand(x):
            return (-mp.log(x))**(a-1)*mp.polylog(b, z*x)/(1-z*x)
        return z*mp.quad(integrand, cuts)/mp.factorial(a-1)
    components = {(a, b): mp.im(direct_double(a, b))
                  for a, b in ((4, 1), (3, 2), (2, 3))}
    def s4_integrand(x):
        return (-mp.log(x))**3*mp.log1p(x*x)/(1+x*x)
    lhs = -mp.quad(s4_integrand, cuts)/6
    beta4 = mp.im(mp.polylog(4, 1j))
    rhs = (4*components[4, 1]-3*components[3, 2]-9*components[2, 3])/7
    rhs += mp.pi**5/224-mp.mpf(27)/224*mp.catalan*mp.zeta(3)-2*beta4*mp.log(2)
    error = abs(lhs-rhs)
    threshold = mp.mpf(10)**(-(dps-8))
    return {"source_label": "gauss:eq:S4-closed", "analytic_status": "conjectural",
            "evidence_status": "Numerical diagnostic only; agreement is not an analytic proof",
            "method": "S4 generating-function integral versus three independent double-polylogarithm integrals",
            "mpmath_dps": dps, "independent_integrals": 4,
            "gaussian_components": {f"g{a}{b}": mp.nstr(value, dps)
                                    for (a, b), value in components.items()},
            "S4_integral": mp.nstr(lhs, dps), "candidate_rhs": mp.nstr(rhs, dps),
            "abs_error": mp.nstr(error, 10), "diagnostic_threshold": mp.nstr(threshold, 6),
            "diagnostic_pass": bool(error < threshold)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dps", type=int, default=60)
    parser.add_argument("--numerical", action="store_true")
    args = parser.parse_args()
    if args.dps < 30:
        parser.error("--dps must be at least 30")
    results_dir = ROOT/"results"
    results_dir.mkdir(parents=True, exist_ok=True)
    exact = exact_replay()
    exact_path = results_dir/"weight5_replay.json"
    exact_path.write_text(json.dumps(exact, indent=2)+"\n", encoding="utf-8")
    print("Exact replay passed: 2 shuffle rows, 15 labelled interleavings, 1 linear combination.")
    print(exact_path)
    if args.numerical:
        numerical = numerical_s4(args.dps)
        numerical_path = results_dir/"S4_numeric_check.json"
        numerical_path.write_text(json.dumps(numerical, indent=2)+"\n", encoding="utf-8")
        print(f"S4 diagnostic: {numerical['independent_integrals']} independent integrals; "
              f"absolute discrepancy {numerical['abs_error']}; "
              f"threshold passed: {numerical['diagnostic_pass']}.")
        print("S4 analytic status remains conjectural.")
        print(numerical_path)


if __name__ == "__main__":
    main()
