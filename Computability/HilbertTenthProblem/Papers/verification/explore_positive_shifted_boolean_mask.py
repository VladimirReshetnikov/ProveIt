#!/usr/bin/env python3
"""Exact negative-domain mask exclusion and positive native-plane offsets."""
from itertools import product
from pathlib import Path
import json


def v2(n):
    assert n > 0
    return (n & -n).bit_length()-1


def digits(n, radix, width):
    out = []
    for _ in range(width):
        n, d = divmod(n, radix)
        out.append(d)
    assert n == 0
    return out


def verify():
    negative_cases = 0
    max_defect = 0
    for bits in range(2,11):
        L = 1 << bits
        for M in range(1,L):
            threshold = bits+M.bit_count()
            d = v2(M)
            assert (M-1).bit_count() == M.bit_count()-1+d
            for s in range(1,M+1):
                a, z = s-1, M-s
                carry = a.bit_count()+z.bit_count()-(M-1).bit_count()
                assert 0 <= carry <= bits-1-d
                r = (L+s)*(L-1)+M
                assert r == L*L+a*L+z
                assert r.bit_count() == 1+a.bit_count()+z.bit_count()
                assert r.bit_count() < threshold
                max_defect = max(max_defect,threshold-r.bit_count())
                negative_cases += 1

    # q=4 makes L=q^7=128^2. This checks the local mask, without
    # pretending q itself aligns single radix-128 fields.
    q, R, N = 4, 128, 2
    L = q**7
    lam = (L-1)//127
    M = 125*lam
    shifted_cases = 0
    accepted_words = 0
    for Pprime in range(1,L+lam+1):
        P = Pprime-lam
        r = (L-P)*(L-1)+M
        assert -lam < P <= L and r > 0
        accepted = r.bit_count() >= 13*N
        expected = 0 <= P < L and P & M == 0
        assert accepted == expected
        if accepted:
            assert set(digits(P,R,N)) <= {0,2}
            assert set(digits(Pprime,R,N)) <= {1,3}
            assert r % 2 == 1
            accepted_words += 1
        shifted_cases += 1
    assert accepted_words == 2**N

    bootstrap = []
    for q in (4,8,16,32,64,128,129,131):
        L = q**7
        assert (L-1)%127 == 0
        lam, D0, n = (L-1)//127, q**13, q**6
        M = 125*lam
        for Pprime in sorted(set((1,max(1,lam-1),lam,lam+1,L+lam))):
            P = Pprime-lam
            r = (L-P)*(L-1)+M
            assert -lam < P <= L
            assert 2*n < L < 2*M
            assert M <= r < 2*L*L < 2*n**3
            assert D0 > n*n and n >= 64
            assert D0*D0 > 2*r+1
            assert 8*r < D0*D0
            assert D0 < r*r
        assert (L-(L+1))*(L-1)+M < 0
        bootstrap.append({'q':q,'power_of_two':q & (q-1) == 0,
                          'extreme_signed_domain_and_scale_bounds':'PASS'})

    q, R = 128, 128
    L, lam = q**7, (q**7-1)//127
    good, bad = [1,3,1,1,1,1,1], [129,2,1,1,1,1,1]
    pack = lambda fields: sum(a*q**i for i,a in enumerate(fields))
    assert pack(good) == pack(bad) == lam+2*q
    P = pack(bad)-lam
    r = (L-P)*(L-1)+125*lam
    assert P == 2*q and r.bit_count() == 13*7
    assert all(a > 0 for a in bad) and bad[0] >= q and bad[1] not in (1,3)

    local_cases = 0
    valid_local_cases = 0
    for n,b,y in product(range(9),range(2),range(2)):
        for u in product(range(2),repeat=5):
            old = n+22*y+6*(u[0]+u[1]-b)+7*u[2]-11*u[3]-14*u[4]
            B,Y = 1+2*b,1+2*y
            U = [1+2*t for t in u]
            # Sum of eight separately shifted native neighbor cells.
            neighbors = 8+2*n
            native = neighbors+22*Y+6*(U[0]+U[1]-B)+7*U[2]-11*U[3]-14*U[4]
            assert native == 18+2*old
            inclusive = 9+2*(n+b)
            native2 = inclusive+22*Y+6*(U[0]+U[1])+7*(U[2]-B)-11*U[3]-14*U[4]
            assert native2 == native
            local_cases += 1
            valid_local_cases += old == 0
    return {
        'status':'PASS',
        'scope':'Negative-domain mask lemma, shifted-word interface, explicit field alias and local affine offset only; no complete Life or universal certificate.',
        'proof':'../1980/EXPLORATION_POSITIVE_SHIFTED_BOOLEAN_MASK.md',
        'arbitrary_mask_negative_cases':negative_cases,
        'binary_lengths':[2,10],
        'minimum_proved_threshold_defect':1,
        'maximum_observed_threshold_defect':max_defect,
        'complete_shifted_word_cases':shifted_cases,
        'accepted_shifted_words':accepted_words,
        'shifted_complete_sample':{'q':4,'radix':128,'digits':2},
        'bootstrap_cases':bootstrap,
        'field_bound_alias':{'q':128,'canonical_fields':good,
                             'positive_invalid_fields':bad,'P':P,
                             'identical_packed_word':True,'mask_passes':True,
                             'not_claimed_to_satisfy_Life_or_torus':True},
        'local_offset_cases':local_cases,
        'locally_satisfying_assignments':valid_local_cases,
        'native_local_offset':'18*Jfield',
        'explicit_unshared_adaptation_operations':{
            'global_Pprime_minus_lambda':1,'construct_Jfield_geometry':2,
            'add_18Jfield_to_local_rhs':2,'total':5},
        'positive_necessity':'Uses the previously proved odd-index 43-operation Pell kernel; full large witnesses are not instantiated here.'}


if __name__ == '__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['arbitrary_mask_negative_cases'],'negative cases;',
          result['complete_shifted_word_cases'],'shifted words;',
          result['local_offset_cases'],'local offsets',flush=True)
