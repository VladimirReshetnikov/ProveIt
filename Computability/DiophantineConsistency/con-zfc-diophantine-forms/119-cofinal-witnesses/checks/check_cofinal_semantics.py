#!/usr/bin/env python3
"""Finite regressions for the 512 checkpoint and consecutive-modulus source.

The quantified proofs are COFINAL_PROOF.md and
CONSECUTIVE_MODULUS_PROOF.md. In particular, checking a finite range of
signed V values does not prove the all-integer nonnegativity lemma.
No proof of consistency, unsolvability, or end-to-end compiler correctness
is claimed by this script. All checks remain active under python -O.
"""
from fractions import Fraction
from math import comb, factorial, gcd, isqrt
from pathlib import Path
import argparse
import hashlib
import json


PROOFS = ('COFINAL_PROOF.md', 'CONSECUTIVE_MODULUS_PROOF.md')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_coprime_beta_moduli(t, y):
    moduli = [1+(i+1)*y for i in range(t+1)]
    pairs = 0
    for i, m in enumerate(moduli):
        require(m > y > 0, 'Beta modulus or its range is invalid')
        for n in moduli[i+1:]:
            require(gcd(m, n) == 1, 'Beta moduli are not pairwise coprime')
            pairs += 1
    return pairs


def check_factorial_ratios():
    tested = 0
    canonical = 0
    for n in range(1, 9):
        G = factorial(n)
        # Retain the original candidate fixture, including repeated G
        # when it is already among 1,...,100.
        for f in list(range(1, 101)) + [G, G+1]:
            rho = f*f*n*n
            V = (rho+1)**n
            D = comb(rho+n, n)
            ratio = Fraction(V, D)
            require(G*(1-Fraction(1, 2*f*f)) < ratio <= G,
                    'Squared-radius ratio estimate failed')
            ceiling = (V+D-1)//D
            require((ceiling == f) == (f == G),
                    'Squared-radius factorial fixed point failed')
            require(f*f+n <= rho+1,
                    'Reciprocal digit bound failed')
            if f == G:
                u, v = V+D-D*G-1, D*G-V
                require(u >= 0 and v >= 0,
                        'Canonical factorial ceiling witness is negative')
                require(V+D == D*G+u+1 and D == u+v+1,
                        'Canonical factorial ceiling rows failed')
                canonical += 1
            tested += 1
    return tested, canonical


def check_512_checkpoint():
    canonical = 0
    pairs = 0
    horizons = list(range(1, 13)) + [16, 17, 20, 25]
    for t in horizons:
        F = factorial(t)
        base = F*t*t+1  # The older 512 checkpoint uses the unsquared F.
        V = base**t
        y = V*V+3*F-1
        require(V % F == 1 % F and y % F == 0,
                '512 checkpoint modulus divisibility failed')
        require(y > V*V and y >= F+1,
                '512 checkpoint modulus range failed')
        require((1+t*F)**(t+1) <= V*V,
                '512 checkpoint pending-product bound failed')
        pairs += check_coprime_beta_moduli(t, y)
        canonical += 1

    signed = 0
    for F in range(1, 26):
        for V in range(-50, 51):
            y = V*V+3*F-1
            require(y-F-1 == V*V+2*F-2 >= 0,
                    '512 checkpoint presemantic endpoint bound failed')
            signed += 1
    return canonical, signed, pairs


def check_consecutive_nonnegativity():
    values = list(range(-1000, 1001)) + [-10**20, -10**10, 10**10, 10**20]
    for V in values:
        y = V*(V-1)
        require(y >= 0 and y+1 >= 1,
                'Consecutive-product nonnegativity failed')
        require(y-V*V+V == 0,
                'Consecutive modulus residual was transcribed incorrectly')
        require(V <= 0 or V >= 1,
                'Integer sign dichotomy failed')
        require((y == 0) == (V in (0, 1)),
                'Consecutive-product zero cases failed')
    # These are valid presemantic seed values. No zero-output obstruction
    # belongs in the new positivity proof.
    for V in (0, 1):
        require(V*(V-1)+1 == 1, 'Degenerate proposed output lost its positive seed')
    return len(values)


def check_strict_pending_bound():
    tested = 0
    for t in range(2, 21):
        for F in range(1, 26):
            a = F*t
            if a < 3:
                continue
            L = a+1
            base = a*a+1
            V = base**t
            require(base > (a-1)*L,
                    'First strict pending-product comparison failed')
            require((a-1)**t >= (a-1)**2 >= L,
                    'Second pending-product comparison failed')
            require(V > L**(t+1),
                    'Strict pending-product bound S<V failed')
            require(V >= F+2,
                    'Recovered power lower bound failed')
            y = V*(V-1)
            require(y >= V > L**(t+1) and y >= F+1,
                    'Consecutive modulus misses a required range bound')
            tested += 1
    # Negative control: the a>=3 hypothesis must not silently disappear.
    require((1+1*1*2*2)**2 < (1+1*2)**3,
            'Strict-bound edge-case negative control failed')
    return tested


def check_principal_canonical_modulus():
    tested = 0
    pairs = 0
    wrong_moduli = 0
    horizons = list(range(2, 13)) + [16, 17, 20, 25]
    for t in horizons:
        F = factorial(t)
        rho = F*F*t*t
        V = (rho+1)**t
        y = V*(V-1)
        require(V % F == 1 % F and (V-1) % F == 0 and y % F == 0,
                'Principal canonical modulus divisibility failed')
        require((1+t*F)**(t+1) < V <= y,
                'Principal canonical accumulator bound failed')
        require(y >= F+1 and y-F-1 >= 0,
                'Principal canonical endpoint slack failed')
        require(y < V*V,
                'Principal fixture accidentally retained the old modulus')
        pairs += check_coprime_beta_moduli(t, y)

        # Squaring V without the correction fails the needed divisibility.
        require(F > 1 and (V*V) % F == 1,
                'Wrong-modulus divisibility negative control failed')
        wrong_moduli += 1
        tested += 1
    return tested, pairs, wrong_moduli


def check_cofinal_arithmetic():
    values = 0
    for h in range(-40, 41):
        t = 16+h*h
        require(t >= 16 and isqrt(t-16)**2 == t-16,
                'Square horizon row failed')
        values += 1
    selections = 0
    for bound in range(5001):
        needed = max(0, bound-16)
        h = isqrt(needed)
        if h*h < needed:
            h += 1
        require(16+h*h >= bound,
                'Finite cofinal horizon selection failed')
        selections += 1
    # An unbounded residue class does not justify an arbitrary square
    # restriction. This is a finite check of the proof's negative example.
    require(all(h*h % 3 != 2 for h in range(-200, 201)),
            'Square-residue negative control failed')
    return values, selections


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--proof-dir', type=Path, required=True,
                    help='Directory containing COFINAL_PROOF.md and CONSECUTIVE_MODULUS_PROOF.md')
    args = ap.parse_args()
    counts = {}

    counts['factorial_ratio_candidates'], counts['factorial_canonical_witnesses'] = check_factorial_ratios()
    (counts['checkpoint512_canonical_cases'],
     counts['checkpoint512_signed_output_cases'],
     counts['checkpoint512_beta_coprime_pairs']) = check_512_checkpoint()
    counts['principal_signed_output_cases'] = check_consecutive_nonnegativity()
    counts['principal_strict_pending_bound_cases'] = check_strict_pending_bound()
    (counts['principal_canonical_modulus_cases'],
     counts['principal_beta_coprime_pairs'],
     counts['wrong_modulus_negative_controls']) = check_principal_canonical_modulus()
    (counts['square_horizon_cases'],
     counts['cofinal_selection_cases']) = check_cofinal_arithmetic()
    counts['square_residue_negative_controls'] = 401
    counts['strict_pending_edge_negative_controls'] = 1

    hashes = {name: hashlib.sha256((args.proof_dir/name).read_bytes()).hexdigest()
              for name in PROOFS}
    result = {
        'status': 'PASS',
        'scope': 'Finite regressions only; quantified proofs remain ordinary mathematics.',
        'principal_modulus': 'y = V*(V-1)',
        'principal_horizon': 't = 16+h*h',
        'principal_proof': 'CONSECUTIVE_MODULUS_PROOF.md',
        'checkpoint_proof': 'COFINAL_PROOF.md',
        'checks': counts,
        'proof_sha256': hashes,
        'optimized_python': not __debug__,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
