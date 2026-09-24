#!/usr/bin/env python3
"""Constructive modular filling with an actual fixed-input numerical trace."""
from math import gcd
from pathlib import Path
import json


def order(a, modulus):
    assert modulus > 1 and gcd(a, modulus) == 1
    value = a % modulus
    result = 1
    while value != 1:
        value = value*a % modulus
        result += 1
        assert result <= modulus
    return result


def boolean(n):
    if n < 0:
        return False
    while n:
        n, digit = divmod(n, 3)
        if digit > 1:
            return False
    return True


def split(n):
    a = b = 0
    power = 1
    while n:
        n, digit = divmod(n, 3)
        if digit:
            a += power
        if digit == 2:
            b += power
        power *= 3
    return a, b


def valuation(r):
    carry = result = 0
    while r:
        r, digit = divmod(r, 3)
        carry = (2*digit+carry)//3
        result += carry
    return result


def toy():
    m, R, g, K, I, hs, hz, U, c = 4, 81, 27, 7, 1, 1, 3, 40, 1
    T = R//g
    d = (K+1)*T-1
    B = U-c
    margin = (T*K-1)*B-T*(hs+hz)-I*(R-1)
    assert margin > 0 and boolean(U) and boolean(B) and U < R
    h, p = 12, 6
    L = order(pow(R, p, d), d)
    n = d*L
    signs = [1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, -1]
    signs += [1, 1, 1, -1, -1, -1]*n
    u = len(signs)
    assert u == h+p*n and u % 6 == 0
    q = R**u
    H = (q-1)//(R-1)
    J = (q-1)//2
    x = 1
    values = [2*x, 0, 0]
    A0 = A1 = Kp = Km = Z = 0
    weight = 1
    maximum = 0
    for row, sign in enumerate(signs):
        lane = row % 3
        source = values[lane]
        maximum = max(maximum, source)
        assert 0 <= source < R//3
        if row == 1:
            assert source == 0
            Z += weight
        a, b = split(source)
        assert a+b == source and boolean(a) and boolean(b)
        A0 += a*weight
        A1 += b*weight
        if sign == 1:
            Kp += weight
        else:
            Km += weight
        values[lane] += sign
        assert min(values) >= 0
        if row == 11 or (row >= 12 and (row-11) % 6 == 0):
            assert values == [0, 0, 0]
        weight *= R
    assert weight == q and values == [0, 0, 0] and maximum == 3
    D = H-Z
    t = ((R-3)//6)*D
    assert R**3*(A0+A1+Kp-Km) == A0+A1-2*x
    assert min(A0, A1, Kp, Km, Z, D, t) > 0 and 2*x < R
    base = B*H
    base_numerator = T*(base+hs*Kp+hz*D)+I*(q-1)
    unit = T*c*pow(R, h, d) % d
    assert gcd(unit, d) == 1
    M = -base_numerator*pow(unit, -1, d) % d
    F = base
    for j in range(M):
        row = h+p*L*j
        assert row < u and T*c*pow(R, row, d) % d == unit
        F += c*R**row
    numerator = T*(F+hs*Kp+hz*D)+I*(q-1)
    C, remainder = divmod(numerator, d)
    V = F-C
    assert remainder == 0 and 0 < C < F and V > 0
    assert (R*K-g)*C == g*I*(q-1)+R*(V+hs*Kp+hz*D)
    assert F == C+V
    fields = [Kp, Km, Z, D, t-A0, A0, t-A1, A1, U*H-F, F]
    assert all(0 <= f < q and boolean(f) for f in fields)
    assert sum(fields) == 2*H+2*t+U*H and H % 2 == 0
    packed = sum(f*q**i for i, f in enumerate(fields))
    scale = q**10
    r = packed+(scale-1)//2
    assert 2*r+1 == scale+2*packed and r < scale < r*r
    assert r % 2 == 0 and r % 3 == 2 and r >= 27 and scale >= 81
    assert valuation(r) == 10*m*u
    return dict(input=x,radix=R,g=g,K=K,I=I,hs=hs,hz=hz,
                allowed_word=U,optional_bit=c,T=T,route_modulus=d,
                positivity_margin=margin,loop_order=L,loop_repetitions=n,
                rows=u,optional_positions=d,toggled_positions=M,
                maximum_counter_source=maximum,Boolean_fields=len(fields),
                exact_route=True,exact_time=True,positive_C_and_V=True,
                packed_index_bits=r.bit_length(),central_valuation=10*m*u,
                even_index=True,
                scope='Complete materialized numerical trace and merged-route arithmetic. Toy constants are not claimed to be a compiled Sidon graph. Positive Pell auxiliaries follow from the general converse and are not materialized.')


def verify():
    cases = 0
    for d in range(2, 48):
        if gcd(3, d) != 1:
            continue
        for m in range(2, 6):
            R = 3**m
            for p in (1, 2, 6):
                L = order(pow(R, p, d), d)
                unit = 3*pow(R, 2, d) % d
                assert gcd(unit, d) == 1
                for residual in range(d):
                    M = -residual*pow(unit, -1, d) % d
                    assert 0 <= M < d
                    assert (residual+M*unit) % d == 0
                    assert all(3*pow(R, 2+p*L*j, d) % d == unit for j in range(M))
                    cases += 1
    return dict(status='PASS_MODULAR_FILL_MERGED_WORD',residue_fill_cases=cases,
                toy=toy(),proof='../1980/EXPLORATION_MODULAR_FILL_MERGED_WORD.md',
                scope='General constructive residue-filling lemma with explicit positivity inequality and unchanged numerical counter trace. A full application to an actual empty controller is a separate gate; no new universal bound.')


if __name__ == '__main__':
    receipt = verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(receipt, indent=2))
