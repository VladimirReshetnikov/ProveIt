#!/usr/bin/env python3
"""Finite ternary clause checks and an exact false Rule110 transplant."""
from itertools import product
from pathlib import Path
import json


def words(n):
    result=[0]
    for i in range(n):
        result += [x+3**i for x in result]
    return result


def digits(n):
    result=[]
    while n:
        n,d=divmod(n,3)
        result.append(d)
    return result


def boolean(n):
    return n>=0 and all(d<=1 for d in digits(n))


def valuation_factorial(n,p):
    answer=0
    while n:
        n//=p
        answer+=n
    return answer


def rule110(B,N):
    result=0
    for i in range(N):
        a=B//3**(i-1)%3 if i else 0
        b=B//3**i%3
        c=B//3**(i+1)%3
        result+=(b+c-b*c*(a+1))*3**i
    return result


def verify():
    scalar=0
    for a,b,c,d in product(range(2),repeat=4):
        accepted=a+b==d and d+c==1
        assert accepted==(a+b+c==1 and d==a+b)
        scalar+=1
    packed=accepted=0
    for N in range(1,6):
        q=3**N;J=(q-1)//2
        for A,B,C in product(words(N),repeat=3):
            D=A+B
            actual=boolean(D) and D<q and D+C==J
            expected=all(A//3**i%3+B//3**i%3+C//3**i%3==1 for i in range(N))
            assert actual==expected
            packed+=1;accepted+=actual
    # Padding triples make all four words positive and can fix even parity.
    padding_cases=0
    for N in range(1,5):
        for choices in product(range(3),repeat=N):
            clauses=[tuple(int(i==x) for i in range(3)) for x in choices]
            clauses += [(1,0,0),(0,1,0),(0,0,1)]
            total=sum(a+b+c+a+b for a,b,c in clauses)
            if total%2:clauses.append((0,0,1))
            A=sum(row[0]*3**i for i,row in enumerate(clauses))
            B=sum(row[1]*3**i for i,row in enumerate(clauses))
            C=sum(row[2]*3**i for i,row in enumerate(clauses))
            D=A+B;q=3**len(clauses);J=(q-1)//2
            P=A+q*B+q*q*C+q**3*D
            assert min(A,B,C,D)>0 and D+C==J
            assert boolean(P) and 0<P<q**4 and P%2==0
            padding_cases+=1

    z=dict(q=27,W=27,v=9,quot=3,H=1,I=1,F=1,C=1,B=3,Y=1,U=3,V=4,
           alpha=9,alphaI=8)
    q=z['q'];W=z['W']
    residuals=[q-z['v']*z['quot'],W-3*z['v'],q-1-z['H']*(W-1),
               z['B']-3*z['C'],14*z['C']+4*z['Y']-2*z['U']-3*z['V'],
               2*z['U']+3*z['V']+z['alpha']-q,
               z['I']+z['alphaI']-z['v'],z['I']+W*z['Y']-z['C']-q*z['F']]
    assert residuals==[0]*8 and min(z.values())>0
    fields=[z['U'],z['V'],z['Y'],z['B']+z['H']]
    assert all(boolean(x) and 0<x<q for x in fields)
    P=sum(field*q**i for i,field in enumerate(fields))
    D0=9*q**4;r=D0-3*P-1;n0=3*q*q
    assert P==79572 and D0==4782969 and r==4544252 and n0==2187
    assert 0<P<q**4 and boolean(P) and P%2==r%2==0
    assert n0<r<D0==n0*n0
    vp=valuation_factorial(2*r,3)-2*valuation_factorial(r,3)
    assert vp==14 and D0==3**14
    actual_Y=rule110(z['B'],3)
    assert actual_Y==4 and z['Y']==1
    return dict(status='TERNARY_LOCAL_CONSTRAINTS_PASS',
                scalar_clause_cases=scalar,packed_clause_cases=packed,
                accepted_packed_clauses=accepted,positive_even_padding_cases=padding_cases,
                clause_schedule=[['D','+','A','B'],['clause_sum','+','D','C']],
                clause_equality=['clause_sum','J'],
                extra_repunit_check=[['twice_J','*',2,'J']],
                extra_repunit_equality=['twice_J','q_minus_one'],
                transplant_counterexample=z,transplant_outer_residuals=residuals,
                packed_P=P,scale=D0,r=r,n0=n0,central_binomial_valuation=vp,
                actual_Rule110_output=actual_Y,
                full_positive_Pell_extension='The base-three kernel theorem applies: q is a power of3, P is bounded ternary Boolean and even. Enormous Pell witnesses are not materialized.',
                proof_note='../1980/EXPLORATION_TERNARY_LOCAL_CONSTRAINTS.md',
                scope='Two-addition clause interface with external Boolean planes and repunit. Repeated-variable incidence, computation semantics, input and halt encoding remain unpaid. The direct Rule110 transplant is refuted; no complete improved universal certificate is claimed.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],result['packed_clause_cases'],'packed cases;',
          result['positive_even_padding_cases'],'positive even padding cases')
