#!/usr/bin/env python3
"""Exact local and input checks, without a complete machine-interface claim."""
from itertools import product
from collections import Counter
from pathlib import Path
import json


def word(raw):
    value=0
    place=1
    while raw:
        value+=(raw&1)*place
        place*=3
        raw>>=1
    return value


def residues(bits,borrow=False):
    a,b,c,d,e=bits
    return c-d-e, (a+d-b-e if borrow else a+e-b-d)


def expected(a,c,borrow=False):
    d=(1-a)*c if borrow else a*c
    return a^c,d,c-d


def verify():
    all_bits=list(product(range(2),repeat=5))
    scalar_cases=two_cell_cases=ripple_cases=0
    for borrow in (False,True):
        solutions=Counter()
        for bits in all_bits:
            a,b,c,d,e=bits
            holds=residues(bits,borrow)==(0,0)
            assert holds==((b,d,e)==expected(a,c,borrow))
            if holds:
                solutions[a,c]+=1
            scalar_cases+=1
        assert set(solutions.values())=={1} and len(solutions)==4
        for low in all_bits:
            for high in all_bits:
                packed=tuple(x+3*y for x,y in zip(low,high))
                assert (residues(packed,borrow)==(0,0)) == (
                    residues(low,borrow)==(0,0) and residues(high,borrow)==(0,0))
                two_cell_cases+=1
        for width in range(1,9):
            for raw in range(1<<width):
                a_word=word(raw)
                b_word=c_word=d_word=e_word=0
                control=1
                raw_output=0
                for j in range(width):
                    a=(raw>>j)&1
                    b,d,e=expected(a,control,borrow)
                    b_word+=b*3**j
                    c_word+=control*3**j
                    d_word+=d*3**j
                    e_word+=e*3**j
                    raw_output+=b<<j
                    control=d
                assert residues((a_word,b_word,c_word,d_word,e_word),borrow)==(0,0)
                assert c_word==1+3*d_word-control*3**width
                assert e_word==0 or e_word in (3**j for j in range(width))
                target=raw-1 if borrow else raw+1
                assert raw_output==target%(1<<width)
                assert control==(int(raw==0) if borrow else int(raw==(1<<width)-1))
                ripple_cases+=1
    four_field_candidates=four_field_accepted=classified_endpoints=0
    for width in range(1,9):
        q=3**width
        J=(q-1)//2
        words={word(raw):raw for raw in range(1<<width)}
        for d in words:
            e=2*d+1
            if e not in words:
                continue
            k=next(k for k in range(width) if e==3**k)
            assert d==(3**k-1)//2
            classified_endpoints+=1
        for borrow in (False,True):
            for a,raw_a in words.items():
                for d in words:
                    four_field_candidates+=1
                    e=2*d+1
                    b=a+d-e if borrow else a+e-d
                    if e not in words or b not in words:
                        continue
                    four_field_accepted+=1
                    raw_b=words[b]
                    assert raw_b==raw_a-1 if borrow else raw_b==raw_a+1
                    assert (a+b+d+e)%2==0
                    packed=a+q*b+q*q*d+q**3*e
                    assert 0<packed<q**4 and packed%2==0
                    fa,fb,fd,fe=(J+x for x in (a,b,d,e))
                    assert fe+J==2*fd+1
                    assert (fa+fd==fb+fe) if borrow else (fa+fe==fb+fd)
                    native_packed=fa+q*fb+q*q*fd+q**3*fe
                    assert all(0<x<q for x in (fa,fb,fd,fe))
                    assert native_packed%2==0
    pairs=represented_values=0
    for width in range(1,8):
        q=3**width
        J=(q-1)//2
        tracks=[word(raw) for raw in range(1<<width)]
        counts=Counter()
        for first in tracks:
            for second in tracks:
                value=first+second
                assert 0<=value<q
                counts[value]+=1
                assert (J+first)+(J+second)==value+(q-1)
                pairs+=1
        assert set(counts)==set(range(q))
        for value,count in counts.items():
            current=value
            ones=0
            while current:
                current,digit=divmod(current,3)
                ones+=digit==1
            assert count==2**ones
            represented_values+=1
    assert 12+9==1+2*10
    assert all(n in [word(r) for r in range(8)] for n in (12,9,1,10))
    assert 12%3+9%3 != 1%3+2*(10%3)
    return dict(status='PASS_LOCAL_AND_INPUT_LEMMAS_ONLY',scalar_assignments=scalar_cases,
                complete_two_cell_assignments=two_cell_cases,ripple_chains=ripple_cases,
                four_field_candidate_pairs=four_field_candidates,
                four_field_accepted_ripples=four_field_accepted,
                classified_endpoint_pairs=classified_endpoints,
                raw_input_pairs=pairs,represented_values_by_width=represented_values,
                local_operations=3,local_histogram={'+':3,'*':0},
                four_field_ripple_operations=4,
                four_field_native_ripple_operations_with_J_available=5,
                raw_input_operations=1,native_positive_link_if_qminus1_available=2,
                direct_halfadder_counterexample=[12,9,1,10],
                proof='../1980/EXPLORATION_TERNARY_COUNTER_CONTROL.md',
                scope='Three-addition ternary Boolean counter/control cells; one-addition native ternary input split. The binary significance of a ripple track differs from that input split. Complete control, wiring, masks, positive adapters and universal input conversion are not constructed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,indent=2))
