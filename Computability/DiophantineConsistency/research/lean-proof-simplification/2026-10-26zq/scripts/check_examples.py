#!/usr/bin/env python3
"""Inspect exact witnesses and arithmetic controls; Lean contains the proofs.

Examples:
  python3 scripts/check_examples.py
  python3 scripts/check_examples.py --cyclic 12 8 7
  python3 scripts/check_examples.py --affine 6 9 17
"""
import argparse
import json
from math import gcd, prod


def cyclic_subset(T: int, a: int, target: int) -> dict:
    if not 0 < a < T:
        raise ValueError("The theorem requires 0 < cardinality < modulus.")
    sigma = a * (a - 1) // 2
    delta = (target - sigma) % T
    q, r = divmod(delta, a)
    subset = [i + q + int(i >= a - r) for i in range(a)]
    assert len(set(subset)) == a and 0 <= min(subset) <= max(subset) < T
    assert sum(subset) % T == target % T
    return {"T": T, "cardinality": a, "target": target % T, "sigma": sigma,
            "delta": delta, "quotient": q, "remainder": r,
            "subset": subset, "sum_mod_T": sum(subset) % T}


def affine_subset(C0: int, T: int, target: int) -> dict:
    if not 0 < C0 < T:
        raise ValueError("The affine theorem requires 0 < C0 < T.")
    target %= C0 * T
    a = target % C0 or C0
    coordinate = ((target - a) // C0) % T
    subset = cyclic_subset(T, a, coordinate)["subset"]
    weights = [1 + C0 * z for z in subset]
    assert sum(weights) % (C0 * T) == target
    return {"C0": C0, "T": T, "target": target, "cardinality": a,
            "coordinate_target": coordinate, "subset": subset, "weights": weights,
            "weight_sum_mod_C0T": sum(weights) % (C0 * T)}


def controller_certificate() -> dict:
    primes = [47, 2011, 120199]
    residues = [26, 1995, 114787]
    modulus = prod(primes)
    K = sum(k * (modulus // p) * pow(modulus // p, -1, p)
            for p, k in zip(primes, residues)) % modulus
    B = pow(2, 94517, modulus)
    r = pow(2, 47 * 977, modulus)
    gamma = (r * (B * B - 1) * (1 + B * K + B * B)) % modulus
    assert pow(B, 120199, modulus) == B
    assert gcd(gamma, modulus) == 1
    return {"modulus": modulus, "K_residue": K, "B_residue": B,
            "radix_977_residue": r, "Gamma_seed_residue": gamma,
            "gcd": gcd(gamma, modulus)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--cyclic", nargs=3, type=int, metavar=("T", "A", "TARGET"))
    group.add_argument("--affine", nargs=3, type=int, metavar=("C0", "T", "TARGET"))
    args = parser.parse_args()
    if args.cyclic:
        result = cyclic_subset(*args.cyclic)
    elif args.affine:
        result = affine_subset(*args.affine)
    else:
        result = {"noncoprime_mod4": [cyclic_subset(4, 2, u) for u in range(4)],
                  "zero_projection_endpoint": affine_subset(6, 9, 0),
                  "other_zero_projection": affine_subset(6, 9, 18),
                  "controller_certificate": controller_certificate(),
                  "boundary_controls": {
                      "n0_converse_fails": gcd(3, 2 * 3 ** 0) == 1 and gcd(3, 2 * 3) != 1,
                      "C0_equal_T_affine_sums_mod4": sorted({0, 1, 3, (1 + 3) % 4})}}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
