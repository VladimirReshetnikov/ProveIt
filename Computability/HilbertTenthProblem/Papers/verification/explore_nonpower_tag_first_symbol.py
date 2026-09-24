"""Conditional first-symbol/first-step facts without a power-radix premise.

The ten separate Boolean masks are hypotheses. The strengthened first-one
statement additionally assumes H Boolean. This is not a 104 soundness proof
and does not implement or assert a new arithmetic saving.
"""
from itertools import product
from pathlib import Path
import json

import explore_general_scaled_tag_transport as previous
import explore_tag_radix_divisibility_omission as omission

tag = previous.tag


def v3(n):
    assert n > 0
    e = 0
    while n % 3 == 0:
        n //= 3
        e += 1
    return e


def check(c, z):
    q, R, H, A = (z[x] for x in ('q', 'R', 'H', 'A'))
    K, Kh, B, U, C = (c[x] for x in ('K', 'Khalf', 'B', 'U', 'C'))
    N, Nb, E, S1, Q, M0, M1 = (z[x] for x in ('N', 'Nbar', 'E', 'S1', 'Q', 'M0', 'M1'))
    Ni, Li, Nf, Lf, L = (z[x] for x in ('Ninit', 'Linit', 'Nfinal', 'Lfinal', 'L'))
    assert q == 3**v3(q) and C == 3**v3(C)
    assert R == C*A and H*(R-1) == q-1 and q >= R and A > Li >= K
    assert Li == 3**v3(Li) and 0 <= Ni <= (Li-1)//2 and tag.boolean(Ni)
    assert all(0 <= z[f] < q and tag.boolean(z[f]) for f in previous.FIELDS)
    assert M0+M1 == L == 2*(N+Nb)+H and 2*Q+S1 == M1
    assert z['S0']+S1 == H and z['Gstar'] == Q+A*H+z['S0']
    assert E+z['Ebar'] == c['c']*H
    assert R*(L+(B-1)*M1) == Kh*(L-Li+q*Lf)
    assert R*(N-3*E-S1+U*M1) == K*(N-Ni+q*Nf)
    assert N % 3 == (S1 % 3 if U % 3 == 0 else (-2*Q) % 3)
    ell, m, cc = v3(Li), v3(R), v3(C)
    assert v3(L) == ell and (L//Li) % 3 == 1
    assert (M0+M1) % 3 == 0 and Q % 3 == S1 % 3 == Ni % 3
    assert z['Gstar'] % 3 == 1 and A % 3 == 0 and m >= cc+1
    result = dict(first_symbol=Ni % 3, one_case=False, H_boolean=tag.boolean(H))
    if Ni % 3 and tag.boolean(H):
        h = 3**m
        assert ell <= m-cc and m > cc
        # Before identifying the first marker's channel, both marker words
        # only have the common lower bound ell on their occupied exponents.
        T0=R//Kh
        assert (T0*M0)%h==0 and (B*T0*M1)%h==0
        assert L%h==Li
        # Q starts with a carry and its first ending is an M1 marker below m.
        end=0
        while (Q//3**end)%3==1:
            end+=1
        assert end<=m-cc and (M1//3**end)%3==1
        assert end==ell and M1 % h == Li and M0 % h == 0
        assert (N+Nb) % h == (Li-1)//2 and N % h == Ni
        prefix = (3*E+S1) % h
        assert 0 <= prefix < K and prefix == Ni % K
        result.update(one_case=True, valuation=m, width_exponent=cc,
                      input_exponent=ell, actual_deleted_prefix=prefix)
    return result


def length_cases():
    q = 3**6
    words = [sum(b*3**i for i, b in enumerate(bs)) for bs in product((0, 1), repeat=6)]
    total = nonpower = 0
    for T0, B, ell, M0, M1 in product((3, 6, 9, 12, 15, 18, 21, 24, 27), (3, 9), range(1, 6), words, words):
        L = M0+M1
        if not L:
            continue
        Li = 3**ell
        numerator = Li+(T0-1)*M0+(B*T0-1)*M1
        if numerator % q or numerator <= 0:
            continue
        Lf = numerator//q
        assert L+q*Lf == Li+T0*M0+B*T0*M1
        assert v3(L) == ell and (L//Li) % 3 == 1
        total += 1
        nonpower += T0 != 3**v3(T0)
    assert total and nonpower
    return dict(exact_length_tuples=total, nonpower_multiplier_tuples=nonpower,
                scope='Only the stated length identity and two Boolean marker masks; no full source claim for these arbitrary multipliers.')


def histories():
    count = one = zero = steps = cutoff = 0
    for beta in (2, 3):
        for a in (2, 3):
            for app in product((0, 1), repeat=a):
                for length in range(beta, beta+3):
                    for initial in product((0, 1), repeat=length):
                        w = tuple(initial); rows = []
                        for _ in range(20):
                            if len(w) < beta:
                                break
                            rows.append(w)
                            w = w[beta:]+(app if w[0] else (0,))
                        if len(w) >= beta:
                            cutoff += 1
                            continue
                        c = tag.constants(beta, app)
                        A = 3**(1+max(map(len, rows))); R = c['C']*A
                        q = R**len(rows); H = (q-1)//(R-1)
                        z = dict.fromkeys(previous.FIELDS, 0)
                        for j, row in enumerate(rows):
                            wt=R**j; s=row[0]; mark=3**len(row); n=tag.value(row)
                            ns=(mark-1)//2; d=tag.value(row[:beta]); e=(d-s)//3
                            z['Q']+=s*ns*wt; z['S'+str(s)]+=wt; z['M'+str(s)]+=mark*wt
                            z['N']+=n*wt; z['Nbar']+=(ns-n)*wt
                            z['E']+=e*wt; z['Ebar']+=(c['c']-e)*wt
                        z['Gstar']=z['Q']+A*H+z['S0']
                        z.update(q=q,R=R,H=H,A=A,Ninit=tag.value(initial),Linit=3**length,
                                 Nfinal=tag.value(w),Lfinal=3**len(w),L=z['M0']+z['M1'])
                        result = check(c, z)
                        count += 1; steps += len(rows)
                        one += result['one_case']; zero += not result['one_case']
    assert one and zero
    return dict(canonical_histories=count, rows=steps, initial_one=one,
                initial_zero=zero, cutoff_unclassified=cutoff)


def verify():
    nonpowers = []
    for k in (5, 6, 8):
        f = omission.family(k)
        z = dict(f['raw_fields'], q=f['q'], R=f['R'], H=f['H'], A=f['A'],
                 Ninit=f['initial'][0], Linit=f['initial'][1], Nfinal=f['terminal'][0],
                 Lfinal=f['terminal'][1], L=f['length_sum'])
        nonpowers.append(check(tag.constants(3, (0, 1, 0)), z))
    # Containment by itself does not bound the first marker by v3(R).
    assert 2*(121+27)+28 == 324
    assert all(tag.boolean(x) for x in (121, 27, 28, 324))
    # A local projector can have non-Boolean H. This is not a full source
    # counterexample, and it also fails the full kernel's fixed unit1 test.
    q=3**20; H=55; R=63396081; A=2348003
    S0=28; S1=27; Q=0; Gstar=Q+A*H+S0
    assert R==27*A and H*(R-1)==q-1 and S0+S1==H
    assert all(tag.boolean(x) for x in (S0,S1,Q,2*Q+S1,Gstar))
    assert not tag.boolean(H) and Gstar%3==0
    return dict(status='PASS_CONDITIONAL_NONPOWER_FIRST_SYMBOL',
                length=length_cases(), histories=histories(),
                full_nonpower_zero_cases=len(nonpowers),
                local_scope_examples=dict(containment_marker_beyond_next_head=True,
                                          nonboolean_H_projector=True, projector_fails_required_unit=True),
                proof='../1980/EXPLORATION_NONPOWER_TAG_FIRST_SYMBOL.md',
                review='Author and two independent complete proof/source reviews and fresh verification runs PASS on the corrected proof; proof and arithmetic frozen.',
                scope='Exact first marker and first read symbol without R being a power; additionally assuming H Boolean, a first-one input has its complete first deleted prefix recovered. Ten unpacked Boolean masks are hypotheses. No general later-history recovery or 104 soundness claim.')


if __name__ == '__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    print(result)
