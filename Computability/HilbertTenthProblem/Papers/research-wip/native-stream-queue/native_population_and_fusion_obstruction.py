"""A population excess defeats a naive geometry/AND-core concatenation.

The constructed tuples satisfy the recoder's retained scalar equations
and the proposed single population equation, with a complete positive
native extension guaranteed by the raw geometry theorem. They have a
wrong dilation output. No full fixed-tag history or false universal
polynomial zero is asserted.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random


def population(n):
    assert n >= 0
    return n.bit_count()


def truth_fields(scale, H, M, Z):
    return (16*(scale-H-M+Z)-15, 16*(H-Z)+4,
            16*(M-Z)+2, 16*Z+8)


def packing(fields, base):
    return sum(f*base**j for j,f in enumerate(fields))


def counterexample(width, duration, high_bits=0, high_H=0, high_M=0):
    """Exact finite member of the all-width/all-dyadic-duration family."""
    D, n = width, duration
    assert D >= 3 and n >= 2 and n & (n-1) == 0
    assert high_bits >= 0
    Th = 1 << high_bits
    assert 0 <= high_H < Th and 0 <= high_M < Th
    high_Z = high_H & high_M
    q, Q = 1 << n, 1 << (D*(n+1))
    B = (1 << (D-1))*Q
    P = B**n
    J = (P-1)//(B-1)
    S = q*P
    K = (S-1)//(2*B-1)
    R = ((1 << D)-1)*J
    x, z, A, Ahat = 1, 2, Q+1, Q+2
    ell, input_slack, gap = n, q-1, Q-q-2
    duration_quotient = (J-n)//(B-1)
    duration_slack = B-1-n
    output_slack = S-Ahat
    quotient_hat = 2
    loader_repunit = (Q-1)//((1 << D)-1)
    assert min(input_slack,gap,duration_quotient,duration_slack,output_slack) > 0
    # Every retained scalar recoder comparison, including both projections.
    assert q == x+input_slack
    assert Q == q+z+gap
    assert P == (B-1)*J+1
    assert S == (2*B-1)*K+1
    assert J == (B-1)*duration_quotient+ell
    assert ell+duration_slack == B-1
    assert Ahat == (Q-1)*(quotient_hat-1)+z+1
    assert Ahat+output_slack == S
    assert ((1 << D)-1)*loader_repunit == Q-1
    assert R > B > Q > q and 0 < x < q
    assert n < B-1 and ell & (ell-1) == 0
    # Any positive program bound below n can still set ell=bound+gap.
    program_E, program_duration_gap = n-1, 1
    assert program_E+program_duration_gap == ell
    L = B*S
    Hr, Mr, Zr = B*x*J+n, B*K+n-1, B*A
    assert 0 <= max(Hr,Mr,Zr) < L
    assert (Hr & Mr) == B and Zr != B
    true_fields = truth_fields(L,Hr,Mr,B)
    low_fields = truth_fields(L,Hr,Mr,Zr)
    assert min(true_fields+low_fields) > 0
    assert sum(true_fields) == sum(low_fields) == 16*L-1
    low_base = 16*L
    exponent = low_base.bit_length()-1
    assert low_base == 1 << exponent
    assert sum(population(v) for v in true_fields) == exponent
    differences = tuple(population(a)-population(b) for a,b in zip(low_fields,true_fields))
    assert differences == (2-D,D-2,D-1,1)
    assert sum(population(v) for v in low_fields) == exponent+D
    # A correct arbitrary high AND contributes exactly log2(Th) more bits.
    H, M, Z = Hr+L*high_H, Mr+L*high_M, Zr+L*high_Z
    T = L*Th
    native_base = 16*T
    fields = truth_fields(T,H,M,Z)
    classes = (Th-high_H-high_M+high_Z-1,
               high_H-high_Z,high_M-high_Z,high_Z)
    assert min(classes) >= 0
    assert sum(population(v) for v in classes) == high_bits
    assert fields == tuple(a+low_base*b for a,b in zip(low_fields,classes))
    assert all(0 < v < native_base for v in fields)
    assert sum(fields) == native_base-1
    field_index = packing(fields,native_base)
    assert population(field_index) == native_base.bit_length()-1+D
    assert 0 < R < P < native_base and R & 1 == 1
    assert population(R) == D*n
    fused_index = R+native_base*field_index
    fused_scale = Q*native_base
    assert fused_index & 1 == 1
    assert fused_index > fused_scale and fused_index >= 9
    assert fused_scale == 1 << population(fused_index)
    # Hence raw geometry47 (in its r>=9,r>q extension) has a full positive
    # native witness tuple at this index/scale. We do not expand that tuple.
    assert Z != (H & M)
    assert z != 1  # spread_D(1)=1
    assert Q != q**D
    return dict(D=D,n=n,q=q,Q=Q,B=B,P=P,J=J,K=K,S=S,R=R,
        x=x,z=z,Ahat=Ahat,quotient_hat=quotient_hat,input_slack=input_slack,
        power_gap=gap,duration_quotient=duration_quotient,duration_slack=duration_slack,
        fusion_output_slack=output_slack,loader_repunit=loader_repunit,
        program_E=program_E,program_duration_gap=program_duration_gap,
        low_scale=L,low_words=[Hr,Mr,Zr],low_true_output=B,
        high_scale=Th,high_words=[high_H,high_M,high_Z],
        full_scale=T,full_words=[H,M,Z],fields=list(fields),
        field_index=field_index,native_base=native_base,
        fused_index=fused_index,fused_scale=fused_scale,
        population_changes=list(differences),
        population_R=population(R),population_fields=population(field_index),
        population_fused=population(fused_index))


def verify():
    rng = random.Random(870303)
    cases = 0
    digest = hashlib.sha256()
    for D in range(3,19):
        for n in (2,4,8,16,32,64):
            for case in range(8):
                high_bits = 0 if case == 0 else rng.randrange(1,25)
                scale = 1 << high_bits
                c = counterexample(D,n,high_bits,rng.randrange(scale),rng.randrange(scale))
                digest.update(hex(c['fused_index']).encode())
                digest.update(hex(c['fused_scale']).encode())
                cases += 1
    # Separate local carry computation: derive all four population changes
    # directly from the low integer blocks, without truth_fields or packing.
    carry_cases = 0
    for D in range(3,25):
        for n in (2,4,8,16,32):
            Q=1 << (D*(n+1)); B=(1 << (D-1))*Q
            P=B**n; J=(P-1)//(B-1); S=(1 << n)*P; K=(S-1)//(2*B-1)
            C=S-J-K
            assert C % B == B-2 and (C//B) % 2 == 0
            assert population(C+Q)-population(C) == 2-D
            assert population(J-1-Q)-population(J-1) == D-2
            assert population(K-1-Q)-population(K-1) == D-1
            assert population(Q+1)-population(1) == 1
            carry_cases += 1
    return dict(status='PASS_NATIVE_POPULATION_AND_FUSION_OBSTRUCTION',
        exact_outer_plus_population_cases=cases,independent_local_carry_cases=carry_cases,
        family_digest=digest.hexdigest(),
        examples=[counterexample(3,2),counterexample(3,4,5,19,23),counterexample(4,2,3,6,3)],
        theorem_scope='For every fixed width D>=3 and arbitrarily large dyadic n, '
            'the retained recoder scalar constraints and the proposed single '
            'concatenated population equation have full positive native extensions '
            'but yield x=1,z=2 and Q=2^(D(n+1)), not the intended dilation/width. '
            'Any correct independent high AND preserves the defect. No full fixed '
            'tag-history witness, false universal polynomial zero, optimality or '
            'arithmetic improvement is claimed. Native Pell witnesses are proved '
            'to exist by the complete raw geometry theorem, not numerically expanded.')


if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    result=verify()
    path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    print({k:result[k] for k in ('exact_outer_plus_population_cases','independent_local_carry_cases')})
