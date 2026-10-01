"""Arbitrary auxiliary targets after weakening i*c^2 to i*c.

This is a local auxiliary theorem and a limitation of an index-bound
repair, not a full positive zero of the complete87 candidate.
"""
import argparse
from math import gcd
import json
from pathlib import Path

import complete75_normalized_strong87 as parent


def pell_mod(A, n, modulus):
    """Binary powering in (Z/modulus)[sqrt(A^2-1)]."""
    assert A >= 2 and n >= 0 and modulus > 0
    D = (A*A-1) % modulus
    x, y, u, v = 1 % modulus, 0, A % modulus, 1 % modulus
    while n:
        if n & 1:
            x, y = (x*u+D*y*v) % modulus, (x*v+y*u) % modulus
        u, v = (u*u+D*v*v) % modulus, 2*u*v % modulus
        n //= 2
    return x, y


def quotient_mod(T, ell, modulus):
    """chi_T(ell)/T modulo modulus, without expanding chi or its quotient."""
    assert ell > 0 and ell & 1 and T >= 2
    residue = pell_mod(T, ell, T*modulus)[0]
    assert residue % T == 0
    return residue // T


def parameters(A, p, target):
    assert A >= 3 and p >= 3 and p % 4 == 3 and A % p == 0 and target > 0
    f, c = parent.pell(A, p)
    Delta = A*A-1
    assert f*f-Delta*c*c == 1
    assert c % 2 == 1 and c % p == p-1 and gcd(4*p, c) == 1
    u = ((target-p)*pow(4*p, -1, c)) % c
    ell = (4*u+1)*p
    T = Delta*c
    assert ell % 4 == 3 and ell % c == target % c
    assert ell // p % 4 == 1 and ell >= p
    # These are the exact two congruences making j and o integral.
    assert quotient_mod(T, ell, c) == (-target) % c
    assert quotient_mod(T, ell, f) == (-c) % f
    # Independently check the intermediate odd-quotient identity modulo f.
    psi = pell_mod(A, ell, f)[1]
    assert psi == c % f
    assert quotient_mod(T, ell, f) == (-psi) % f
    assert f > 2*c
    return dict(A=A, p=p, target=target, f=f, c=c, Delta=Delta, T=T, u=u, ell=ell)


def full_small(A, target):
    """Only p=3 fixtures are materialized; general indices stay compressed."""
    data = parameters(A, 3, target)
    f, c, Delta, T, ell = (data[n] for n in ('f', 'c', 'Delta', 'T', 'ell'))
    assert ell <= 10000
    chi, y = parent.pell(T, ell)
    V, remainder = divmod(chi, T)
    assert remainder == 0
    j, remainder = divmod(V+target, c)
    assert remainder == 0
    o, remainder = divmod(V+c, f)
    assert remainder == 0
    assert min(j, o, y, V) > 0 and V > c
    assert f*f-Delta*c*c == 1
    assert T*T*(V*V-y*y)+y*y == 1
    assert V == o*f-c == j*c-target
    return dict(A=A, p=3, target=target, ell=ell, c=c,
                V_bits=V.bit_length(), y_bits=y.bit_length(),
                all_auxiliary_coordinates_positive=True)


def verify():
    modular = near = 0
    examples = []
    for p in range(3, 48, 4):
        for multiple in (1, 2, 3, 5):
            A = multiple*p
            for target in (1, p, p+2, p+4, 2*p-1, 5*p):
                data = parameters(A, p, target)
                modular += 1
                if p >= 7 and target == p+4:
                    c, Delta = data['c'], data['Delta']
                    R, n = target, (target+1)//2
                    assert 2*n == R+1 and n < p < 2*n
                    assert 2*p >= R-1 and p != R and R % 4 == 3
                    assert c > A*Delta*Delta and c > 2*(R+2) and c > 2*p
                    assert c > p and p % c != 0
                    near += 1
                    if multiple == 2 and p in (7, 11, 19, 47):
                        examples.append(dict(A=A,p=p,R=R,n=n,
                            c_bits=c.bit_length(),ell_bits=data['ell'].bit_length(),
                            auxiliary_index_multiplier=data['ell']//p,
                            full_Pell_auxiliaries_materialized=False))
    full = [full_small(A,target) for A in (3,6,9) for target in (1,3,7,11)]
    # Literal candidate scope: the sole ic2 operand is changed, while c^2
    # remains live. The theorem above does not assert any full zero here.
    _, source, pairs, polynomial = parent.sources()
    candidate = [(n, op, a, 'R10a') if n == 'ic2' else (n, op, a, b)
                 for n, op, a, b in polynomial]
    assert next(r for r in polynomial if r[0] == 'ic2') == ('ic2','*','i','c2')
    assert len(candidate) == 87 and len(parent.RETAINED) == 19
    assert sum(r[1] == '*' for r in candidate) == 48
    assert pairs == [('eight_units',1)]
    return dict(status='PASS_COMPLETE75_LINEAR_STRONG87_TARGET_CRT',
                modular_auxiliary_cases=modular,near_index_cases=near,
                near_index_examples=examples,full_small_auxiliary_cases=full,
                candidate=dict(operations=87,multiplications=48,additions_subtractions=39,
                               witnesses=19,changed_row=['ic2','*','i','R10a'],
                               no_complete_zero_claim=True),
                scope='The weakened local auxiliary system realizes every positive target '
                      'for p=3 mod4 and A divisible by p. Nearby wrong targets preserve '
                      'the preliminary first-index bounds, but no common first-norm/ratio, '
                      'outer-packing or ordinary-input solution is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print({k:result[k] for k in ('modular_auxiliary_cases','near_index_cases')})
