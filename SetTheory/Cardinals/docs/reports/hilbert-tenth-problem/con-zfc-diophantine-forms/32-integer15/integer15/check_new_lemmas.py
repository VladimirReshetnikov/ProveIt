#!/usr/bin/env python3
"""Finite diagnostics for the new Pell normalization and signed weights.

The universal proofs are in SIGNED15_16_PROOF.md. This program does not search
for a ZFC refutation and does not establish the compiler theorem.
"""
import json
from math import gcd, isqrt
from pathlib import Path


def multiply(x, y, delta):
    a, b = x
    c, d = y
    return a*c+delta*b*d, a*d+b*c


def check():
    orbit_checks = 0
    for t in range(2, 11):
        delta = t*t-1
        eta = t, 1
        starts = [(1, 0)]
        unit = 1, 0
        for exponent in range(1, 4):
            unit = multiply(unit, eta, delta)
            starts.extend([unit, (unit[0], -unit[1])])
        for modulus in range(1, 25):
            unit_mod = 1 % modulus, 0
            exponent = 0
            unit_full = 1, 0
            while True:
                exponent += 1
                unit_full = multiply(unit_full, eta, delta)
                unit_mod = tuple(v % modulus for v in multiply(unit_mod, eta, delta))
                if unit_mod == (1 % modulus, 0):
                    break
                assert exponent <= modulus*modulus
            for start in starts:
                candidate = start
                while candidate[1] <= t+modulus:
                    candidate = multiply(candidate, unit_full, delta)
                a, H = candidate
                assert a*a-delta*H*H == 1
                assert (H-start[1]) % modulus == 0
                assert (a-start[0]) % modulus == 0
                orbit_checks += 1

    coprimality_checks = 0
    for A in range(2, 9):
        for C in range(1, 9):
            for i in (-3, -2, -1, 1, 2, 3):
                J = 4*A-5
                D = (A*A-1)*C*C+1
                E = i*J*D*C*C
                F = (A*A-1)*E*E+1
                G1 = A+F*(C*D+1-A)
                assert D > 1 and F > 1 and G1 > 1
                for residue in range(-4, 5):
                    H = C+F*residue
                    I = (G1*G1-1)*H*H+1
                    assert gcd(D,F) == gcd(D,I) == gcd(F,I) == 1
                    assert (I-D) % F == 0
                    coprimality_checks += 1

    weight_checks = 0
    for stack in range(-999, 1002, 4):
        assert stack % 4 == 1 and stack != 0
        weight = stack+1
        assert weight*weight > abs(stack)
        for P in range(-5, 6):
            for K in range(-5, 6):
                a0 = (P*P-1)*K*K+1
                majorant = P*P+K*K+1
                assert majorant*majorant >= abs(a0)
                # Exact two-radical comparison, with no floating point.
                k = abs(weight)*(majorant+1)
                aa, bb = abs(stack), weight*weight*abs(a0)
                assert k*k > aa+bb
                assert (k*k-aa-bb)**2 > 4*aa*bb
                weight_checks += 1
    return {
        'status':'PASS',
        'scope':'Finite diagnostics supplement the stated universal proofs.',
        'signed_pell_orbit_cases':orbit_checks,
        'pairwise_coprimality_cases':coprimality_checks,
        'signed_weight_cases':weight_checks,
    }


if __name__ == '__main__':
    result=check()
    (Path(__file__).parent/'NEW_LEMMA_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
