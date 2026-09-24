#!/usr/bin/env python3
"""Independent finite audit of the absorbed-center radix-8 history bound."""
from itertools import product
from pathlib import Path
import json


def word(raw):
    value, place = 0, 1
    while raw:
        value += (raw & 1)*place
        raw >>= 1
        place *= 8
    return value


def boolean(value):
    if value < 0:
        return False
    while value:
        value, bit = divmod(value,8)
        if bit > 1:
            return False
    return True


def rule(value):
    assert boolean(value)
    result, place = 0, 1
    for _ in range((value.bit_length()+2)//3+1):
        a = (value//(place//8))%8 if place > 1 else 0
        b, c = (value//place)%8, (value//(8*place))%8
        y = b+c-b*c-a*b*c
        result += y*place
        place *= 8
    return result


def auxiliaries(total, q):
    if not 0 <= total < q:
        return None
    U = V = 0
    place = 1
    while total:
        total, digit = divmod(total,8)
        if digit not in (0,2,3,5):
            return None
        U += int(digit in (2,5))*place
        V += int(digit in (3,5))*place
        place *= 8
    assert 2*U+3*V < q
    return U,V


def check_complete_tuple(m,t,B,Y,U,V,I,F):
    v,W,q = 2**m,8**m,8**(m*t)
    H = (q-1)//(W-1)
    C = B//8
    assert all(z > 0 for z in (B,C,Y,U,V,I,F))
    assert B == 8*C and 0 < I < v
    assert I+W*Y == C+q*F
    rhs = 2*U+3*V
    assert rhs == 119*C+4*Y < q
    assert 119*C < q and 119*B < 8*q
    assert 119*(B+H) < 25*q and 8*B < q
    assert all(boolean(z) for z in (I,F))
    assert all(boolean(z) for z in (Y,U,V,B+H))
    assert all(0 <= z < q for z in (Y,U,V,B+H))
    assert boolean(B)
    # The predecessor bound is checked only after accepting the new system.
    # It is never an enumeration filter.
    assert 56*B < q and 56*Y < q
    old_rhs = C+2*U+3*V
    assert old_rhs == 15*B+4*Y < q
    alpha_new, alpha_old = q-rhs, q-old_rhs
    assert alpha_new > 0 and alpha_old > 0
    assert alpha_new == alpha_old+C
    assert alpha_old == alpha_new-C
    current = 8*I
    for j in range(t):
        bj = (B//W**j)%W
        yj = (Y//W**j)%W
        assert bj == current and bj%8 == 0
        assert yj == rule(bj)
        current = 8*yj
    assert current == 8*F
    assert U%8 == 0
    P = U+q*V+q*q*Y+q**3*(B+H)
    L, D0 = q**6,q**10
    lam = (L-1)//7
    r = (L-P)*(L-1)+6*lam
    assert P < q**4 and r%2 == 0
    assert r.bit_count() == 30*m*t
    assert D0 == 1 << (30*m*t)
    assert D0 < r < (q**5)**3
    return dict(m=m,t=t,I=I,F=F,q=q,B=B,C=C,Y=Y,U=U,V=V,
                alpha=alpha_new,alpha_old=alpha_old,slack_bijection=True,alphaI=v-I,r_bit_count=r.bit_count(),
                source_has_111=any((B//8**j)%512 == 73 for j in range(m*t)))


def verify():
    scalar_cases = 0
    for a,b,c,y,U,V in product(range(2),repeat=6):
        residual = 2*a-b-c+4*y-2*U-3*V
        correct = y == b+c-b*c-a*b*c
        expected_U, expected_V = a ^ (b*c), b ^ c
        assert (residual == 0) == (correct and U == expected_U and V == expected_V)
        assert 0 <= 2*a+4*y <= 6 < 8
        assert 0 <= b+c+2*U+3*V <= 7 < 8
        scalar_cases += 1
    table_candidates = 0
    boundary_candidates = 0
    attempted_final_words = 0
    accepted = []
    no_111 = 0
    for N in range(2,13):
        q = 8**N
        all_words = [word(raw) for raw in range(1 << N)]
        for m in range(2,min(6,N)+1):
            if N%m:
                continue
            t,W,v = N//m,8**m,2**m
            H = (q-1)//(W-1)
            final_words = [word(raw) for raw in range(1,1 << m)]
            for T in all_words:
                table_candidates += 1
                B = T-H
                if B <= 0 or B%8 or 119*(B//8) >= q:
                    continue
                C = B//8
                I = C%W
                if not 0 < I < v:
                    continue
                lower_Y = C//W
                if not boolean(lower_Y):
                    continue
                boundary_candidates += 1
                for F in final_words:
                    attempted_final_words += 1
                    Y = lower_Y+(q//W)*F
                    if 119*C+4*Y >= q:
                        continue
                    pair = auxiliaries(119*C+4*Y,q)
                    if pair is None or not all(pair):
                        continue
                    rec = check_complete_tuple(m,t,B,Y,*pair,I,F)
                    accepted.append(rec)
                    no_111 += not rec['source_has_111']

    canonical = []
    for I in (1,9,65,73,513):
        for t in (1,2,3,4,8,16):
            rows, outputs = [], []
            current = 8*I
            for _ in range(t):
                rows.append(current)
                out = rule(current)
                outputs.append(out)
                current = 8*out
            m = max(3, max(value.bit_length() for value in rows+outputs)//3+3)
            while 2**m <= I:
                m += 1
            W,q = 8**m,8**(m*t)
            B = sum(value*W**j for j,value in enumerate(rows))
            Y = sum(value*W**j for j,value in enumerate(outputs))
            U,V = auxiliaries(119*(B//8)+4*Y,q)
            canonical.append(check_complete_tuple(m,t,B,Y,U,V,I,outputs[-1]))
    assert accepted and no_111 > 0
    return {'status':'PASS',
            'scope':'Independent complete bounded T/final-Y enumeration, exact local truth table and positive canonical outer histories for the proved79 absorbed-center component; no full Pell witnesses or universal interface instantiated.',
            'scalar_cases':scalar_cases,
            'complete_T_words':table_candidates,
            'boundary_candidates':boundary_candidates,
            'final_word_candidates':attempted_final_words,
            'accepted_outer_tuples':len(accepted),
            'accepted_without_source_111':no_111,
            'enumeration':{'total_digits':[2,12],'row_widths':[2,6]},
            'sample_tuples':accepted[:12],
            'canonical_positive_histories':len(canonical),
            'canonical_parameters':[{'I':r['I'],'t':r['t'],'m':r['m'],
                                     'F':str(r['F']),'source_has_111':r['source_has_111']}
                                    for r in canonical],
            'every_candidate_checked_for_actual_moving_trajectory':True,
            'packed_binomial_popcount_checked':True,
            'old_bound_used_as_enumeration_filter':False,
            'new_bound':'119C+4Y<q',
            'positive_slack_bijection_checked_for_every_accepted_and_canonical_tuple':True,
            'parity':'U unit digit zero gives even P and r',
            'source_111_requirement':'Removed; valid positive histories without111 are explicitly included.'}


if __name__ == '__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['complete_T_words'],'complete T words;',
          result['accepted_outer_tuples'],'accepted;',result['accepted_without_source_111'],
          'without111;',result['canonical_positive_histories'],'canonical histories',flush=True)
