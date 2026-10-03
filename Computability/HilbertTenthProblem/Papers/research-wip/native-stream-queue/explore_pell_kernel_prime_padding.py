#!/usr/bin/env python3
"""Elementary prime padding and Boolean CRT coverage in reserved unit cells.

All choices are proof constructions, not free certificate primitives.
"""
from pathlib import Path
from math import gcd, lcm
import argparse
import json

import sympy as sp


def valuation(value, prime):
    out = 0
    while value % prime == 0:
        value //= prime
        out += 1
    return out


def choose_prime(Q, S):
    assert Q >= 2 and S >= 1 and S % 2 == 1 and gcd(Q, S) == 1
    t = int(sp.n_order(Q, S)) if S > 1 else 1
    cyclotomic_index = lcm(2, t)
    A0 = cyclotomic_index*S*Q*(Q-1)
    z = sp.Symbol("z")
    polynomial = sp.Poly(sp.cyclotomic_poly(cyclotomic_index, z), z)
    cyclotomic_value = int(polynomial.eval(A0))
    ell = int(min(sp.factorint(cyclotomic_value)))
    order_Q = int(sp.n_order(Q, ell))
    k = lcm(t, order_Q)
    e = valuation(Q**k-1, ell)
    assert polynomial.TC() == 1 and cyclotomic_value > 1
    assert sp.isprime(ell) and cyclotomic_value % ell == 0
    assert gcd(ell, cyclotomic_index*S*Q*(Q-1)) == 1
    assert sp.n_order(A0, ell) == cyclotomic_index
    assert (ell-1) % cyclotomic_index == 0
    assert 2 <= k < ell and (ell-1) % k == 0 and pow(Q, k, S) == 1 % S
    return dict(Q=Q, S=S, t=t, cyclotomic_index=cyclotomic_index,
                A0=A0, cyclotomic_value=cyclotomic_value,
                ell=ell, k=k, e=e, order_Q_mod_ell=order_Q)


def prepare_orbit(Q, S, ell, k, padding_exponent, shift=2):
    assert Q >= 2 and S >= 1 and S % 2 == 1
    assert sp.isprime(ell) and gcd(ell, S*Q*(Q-1)) == 1
    assert 2 <= k < ell and (ell-1) % k == 0
    assert pow(Q, k, S) == 1 % S and pow(Q, k, ell) == 1
    e = valuation(Q**k-1, ell)
    assert padding_exponent > e
    N = ell**padding_exponent
    ell_power = ell**e
    T = N//ell_power
    C0, modulus = S*ell_power, S*N
    assert T > C0 and shift >= 2
    assert shift+k*(T-1) < N-1 and shift+1 < N-1
    index_of_t = [-1]*T
    value, multiplier = 1, pow(Q, k, modulus)
    for j in range(T):
        assert (value-1) % C0 == 0
        coordinate = (value-1)//C0
        assert 0 <= coordinate < T and index_of_t[coordinate] == -1
        index_of_t[coordinate] = j
        value = value*multiplier % modulus
    assert value == 1 and -1 not in index_of_t
    return dict(Q=Q, S=S, ell=ell, k=k, e=e, N=N, T=T,
                C0=C0, modulus=modulus, shift=shift,
                inverse_shift=pow(pow(Q, shift, modulus), -1, modulus),
                index_of_t=index_of_t)


def select_subset(orbit, target):
    Q, ell, C0, T, modulus = (orbit[key] for key in ("Q", "ell", "C0", "T", "modulus"))
    normalized = target*orbit["inverse_shift"] % modulus
    epsilon = 1 if normalized % ell == 0 else 0
    adjusted = (normalized-epsilon*Q) % modulus
    cardinality = adjusted % C0
    assert 1 <= cardinality < C0 < T and gcd(cardinality, T) == 1
    z = (adjusted-cardinality)//C0
    start = (z-cardinality*(cardinality-1)//2)*pow(cardinality, -1, T) % T
    positions = [orbit["shift"]+orbit["k"]*orbit["index_of_t"][(start+j) % T]
                 for j in range(cardinality)]
    if epsilon:
        positions.append(orbit["shift"]+1)
    assert len(positions) == len(set(positions))
    assert min(positions) >= 2 and max(positions) < orbit["N"]-1
    residue = sum(pow(Q, position, modulus) for position in positions) % modulus
    assert residue == target % modulus
    return dict(positions=positions, cardinality=cardinality, epsilon=epsilon,
                progression_start=start, sum_modulus=residue)


def verify():
    records = []
    total_targets = exhaustive_targets = 0
    for Q, S in ((2, 1), (4, 5), (4, 3), (64, 3)):
        parameters = choose_prime(Q, S)
        ell, k, e = (parameters[key] for key in ("ell", "k", "e"))
        padding_exponent = 2*e+1
        while True:
            N = ell**padding_exponent
            T = N//ell**e
            if T > S*ell**e and 2+k*(T-1) < N-1:
                break
            padding_exponent += 1
        orbit = prepare_orbit(Q, S, ell, k, padding_exponent)
        if orbit["modulus"] <= 10000:
            targets = range(orbit["modulus"])
            exhaustive_targets += orbit["modulus"]
        else:
            targets = sorted({0, 1, orbit["modulus"]-1,
                              *(j*j*104729 % orbit["modulus"] for j in range(101))})
        maximum_cardinality = 0
        epsilon_count = 0
        for target in targets:
            selection = select_subset(orbit, target)
            maximum_cardinality = max(maximum_cardinality, len(selection["positions"]))
            epsilon_count += selection["epsilon"]
            total_targets += 1
        assert pow(Q, orbit["N"], S) == Q % S
        assert pow(Q, orbit["N"], ell) == Q % ell
        assert gcd(pow(Q, orbit["N"], ell)-1, ell) == 1
        records.append(dict(parameters=parameters, padding_exponent=padding_exponent,
                            N=orbit["N"], T=orbit["T"], modulus=orbit["modulus"],
                            targets=len(targets), maximum_subset_size=maximum_cardinality,
                            epsilon_uses=epsilon_count,
                            reserved_low_and_top_cells_untouched=True))
    return dict(status="PASS_ELEMENTARY_PRIME_PADDING_BOOLEAN_CRT",
                targets=total_targets, exhaustive_targets=exhaustive_targets,
                examples=records,
                scope="Mathematical Boolean subset lemma; no arithmetic operations are supplied for free")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix(".json")
    if args.write:
        path.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    else:
        assert result == json.loads(path.read_text(encoding="utf-8"))
    print(result["status"], result["targets"], "targets")
    print(result["examples"])
