#!/usr/bin/env python3
"""Exact full-spectrum checks for the cubic/quadratic Rajan packet family.

No floating point, character traces, or third-party packages are used.
Eigenvalues are represented by their exponents in the sixth roots of unity.
Two complete local characteristic polynomials agree iff these multiplicity
vectors agree. All elements of C3^2 x C2^k are checked for 0 <= k <= 5.
"""

from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd, isqrt
from pathlib import Path
import json


def packet_characters(k):
    """Expand (1+chi+chi^2)(1-psi) product_i(1-eta_i) in the dual group."""
    positive, negative = [], []
    for j, t, mask in product(range(3), range(2), range(1 << k)):
        target = positive if (t + mask.bit_count()) % 2 == 0 else negative
        target.append((j, t, mask))
    assert len(positive) == len(negative) == 3 * (1 << k)
    assert len(set(positive)) == len(positive)
    assert len(set(negative)) == len(negative)
    assert not set(positive).intersection(negative)
    return positive, negative


def spectrum(packet, element):
    """Multiplicity vector of powers of zeta_6, in order 0,...,5."""
    a, b, e_mask = element
    counts = [0] * 6
    for j, t, character_mask in packet:
        quadratic_exponent = (character_mask & e_mask).bit_count() % 2
        exponent = (2 * (j * a + t * b) + 3 * quadratic_exponent) % 6
        counts[exponent] += 1
    return counts


def is_prime(n):
    if n < 2:
        return False
    return all(n % d for d in range(2, isqrt(n) + 1))


def check_family(k):
    positive, negative = packet_characters(k)
    group = list(product(range(3), range(3), range(1 << k)))
    mismatches = []
    agrees = 0
    for element in group:
        pos = spectrum(positive, element)
        neg = spectrum(negative, element)
        observed = pos != neg
        a, b, e_mask = element
        predicted = a == 0 and b != 0 and e_mask == (1 << k) - 1
        assert observed == predicted, (k, element, pos, neg)
        if observed:
            mismatches.append({
                "element": {"chi_exponent_mod3": a, "psi_exponent_mod3": b,
                            "quadratic_exponents_mod2": [(e_mask >> i) & 1 for i in range(k)]},
                "positive_sixth_root_multiplicities": pos,
                "negative_sixth_root_multiplicities": neg,
            })
            # Independently check the closed form for the two exceptional spectra.
            if k == 0:
                expected_pos, expected_neg = [0] * 6, [0] * 6
                expected_pos[0] = 3
                expected_neg[(2 * b) % 6] = 3
            else:
                mult = 3 * (1 << (k - 1))
                expected_pos, expected_neg = [0] * 6, [0] * 6
                expected_pos[0] = mult
                expected_pos[(3 + 2 * b) % 6] = mult
                expected_neg[3] = mult
                expected_neg[(2 * b) % 6] = mult
            assert pos == expected_pos and neg == expected_neg
        else:
            agrees += 1
    n = len(positive)
    # floor(log2(2n)) is computed by exact integer arithmetic.
    d = (2 * n).bit_length() - 1
    actual = Fraction(len(mismatches), len(group))
    claimed_floor = Fraction(1, 1 << d)
    assert d == k + 2
    assert len(mismatches) == 2
    assert actual == Fraction(2, 9 * (1 << k))
    assert claimed_floor == Fraction(1, 4 * (1 << k))
    assert actual < claimed_floor
    # Adding the same characters to both sides preserves local disagreement.
    padded_dimensions = list(range(3 * (1 << k), 4 * (1 << k)))
    assert all((2 * m).bit_length() - 1 == k + 2 for m in padded_dimensions)
    return {
        "k": k, "packet_dimension": n, "group_order": len(group),
        "all_group_elements_checked": len(group),
        "positive_and_negative_global_character_packets_disjoint": True,
        "full_spectrum_agreement_count": agrees,
        "full_spectrum_disagreement_count": len(mismatches),
        "actual_disagreement_density": str(actual),
        "actual_agreement_density": str(1 - actual),
        "rajan_d_n_floor_log2_2n": d,
        "conjectured_disagreement_floor": str(claimed_floor),
        "conjectured_agreement_ceiling": str(1 - claimed_floor),
        "strict_excess_of_actual_agreement": str(claimed_floor - actual),
        "ratio_actual_to_conjectured_disagreement": str(actual / claimed_floor),
        "padded_counterexample_dimensions": padded_dimensions,
        "exceptional_elements_and_spectra": mismatches,
    }


def check_modulus_91():
    logs7 = {pow(3, j, 7): j % 3 for j in range(6)}
    logs13 = {pow(2, j, 13): j % 3 for j in range(12)}
    assert len(logs7) == 6 and len(logs13) == 12
    positive, negative = packet_characters(0)
    fibres = Counter()
    bad = []
    for a in range(91):
        if gcd(a, 91) != 1:
            continue
        x, y = logs7[a % 7], logs13[a % 13]
        fibres[x, y] += 1
        if spectrum(positive, (x, y, 0)) != spectrum(negative, (x, y, 0)):
            bad.append(a)
    assert len(fibres) == 9 and set(fibres.values()) == {8}
    assert len(bad) == 16
    bad_primes = [p for p in range(2, 1001) if is_prime(p) and gcd(p, 91) == 1 and p % 91 in bad]
    assert bad_primes[0] == 29
    assert (logs7[29 % 7], logs13[29 % 13]) == (0, 1)
    return {
        "modulus": 91,
        "chi_definition": "chi modulo 7, chi(3)=omega; 3 has order 6 modulo 7",
        "psi_definition": "psi modulo 13, psi(2)=omega; 2 has order 12 modulo 13",
        "joint_fibres": [{"chi_exponent_mod3": a, "psi_exponent_mod3": b, "size": fibres[a, b]} for a in range(3) for b in range(3)],
        "total_reduced_residue_classes": 72,
        "disagreeing_reduced_residue_classes": bad,
        "disagreement_count": 16,
        "agreement_count": 56,
        "disagreement_density": "2/9",
        "agreement_density": "7/9",
        "smallest_unramified_distinguishing_prime": 29,
        "at_29": {"chi_value": "1", "psi_value": "omega",
                  "first_euler_denominator": "(1-T)^3", "second_euler_denominator": "(1-omega*T)^3"},
        "distinguishing_primes_up_to_1000": bad_primes,
    }


def main():
    family = [check_family(k) for k in range(6)]
    report = {
        "status": "PASS",
        "method": "Exact sixth-root exponent multisets; no traces, floating point, or approximate arithmetic",
        "family_definition": "positive/negative character terms of (1+chi+chi^2)(1-psi) product_i(1-eta_i)",
        "group": "C3 x C3 x C2^k",
        "complete_spectrum_disagreement_criterion": "chi=1, psi!=1, and every eta_i=-1",
        "total_group_elements_checked": sum(x["all_group_elements_checked"] for x in family),
        "k_values_checked": list(range(6)),
        "family_results": family,
        "explicit_dirichlet_example": check_modulus_91(),
        "verification_scope": "The finite family instances and modulus-91 data are checked exhaustively. The proof for all k and its prime-density transfer are mathematical arguments in the accompanying paper.",
    }
    output = json.dumps(report, indent=2)
    out = Path(__file__).resolve().parents[1] / "results" / "rajan_family_exact_checks.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(output + "\n")
    print(output)


if __name__ == "__main__":
    main()
