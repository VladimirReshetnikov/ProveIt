"""Exact two-phase contextual code for the hidden Boolean carry; no compiler."""
import argparse
from itertools import product
import json
from pathlib import Path
import sympy as sp

import native_controller_boolean_carry70 as prior


def boolean_words(length):
    return [sum(bit*3**i for i,bit in enumerate(bits))
            for bits in product((0,1),repeat=length)]


def hidden_path(read, append, length, initial):
    states=[initial]
    for i in range(length):
        label=tuple(F//3**i%3 for F in append+read)
        nxt=prior.hidden_step(states[-1],label)
        if nxt is None:return None
        states.append(nxt)
    return states


def family(n):
    Q=27**n;J=(Q-1)//26;R=14*J;V=12*J
    answer=[]
    for bits in product((0,1),repeat=n):
        p=J+3*sum(bit*27**i for i,bit in enumerate(bits))
        answer.append((bits,(p,R-p),(p,V-2*p)))
    return answer


def code_checks():
    rows=[]
    for n in range(1,6):
        codes=family(n);ell=3*n;Q=3**ell
        tested=computations=returns=0
        for bits,A,B in codes:
            assert min(A+B)>0
            assert all(all(F//3**i%3 in (0,1) for i in range(ell)) and F<Q for F in A+B)
            for other,AA,BB in codes:
                for entry in (0,1):
                    forward=hidden_path(A,BB,ell,entry)
                    backward=hidden_path(B,AA,ell,entry)
                    assert (forward is not None)==(entry==0)
                    assert (backward is not None)==(entry==0 and bits==other)
                    if forward is not None:
                        assert forward[-1]==0
                        assert forward==[0]+[v for bit in other for v in (1,bit,0)]
                        computations+=1
                    if backward is not None:
                        assert backward[-1]==0
                        assert backward==[0]+[v for bit in bits for v in (1,bit,0)]
                        returns+=1
                    tested+=2
        rows.append(dict(concatenated_bits=n,physical_cells=ell,symbols=len(codes),
                         microscopic_paths_tested=tested,computation_paths=computations,
                         identity_return_paths=returns))
    return dict(domains=rows,paths_tested=sum(r['microscopic_paths_tested'] for r in rows),
                smallest_codes=[dict(logical_bit=bits[0],ordinary=list(A),temporary=list(B))
                                for bits,A,B in family(1)])


def minimum_checks():
    rows=[]
    for ell in range(1,4):
        Q=3**ell;values=boolean_words(ell);native=set(values);groups={}
        for p,a1 in product(values,repeat=2):
            R=p+a1;V=Q-1-R
            if V-2*p in native:
                groups.setdefault(R,[]).append(((p,a1),(p,V-2*p)))
        multiple={R:items for R,items in groups.items() if len(items)>1}
        if ell<3:assert not multiple
        else:
            assert set(multiple)=={14}
            assert set(multiple[14])=={((1,13),(1,10)),((4,10),(4,4))}
        rows.append(dict(physical_cells=ell,ordinary_rail_pairs=len(values)**2,
                         families_with_two_or_more_symbols=len(multiple)))
    return dict(domains=rows,scope='Only the full computation plus identity-return template with hidden boundary0')


def external_algebra():
    h,u0,u1,v0,v1,p,r,c,kappa=sp.symbols('h u0 u1 v0 v1 p r c kappa')
    compute=13*h+u0*p+u1*(14-p)+v0*r+v1*(12-2*r)
    return_rule=13*h+u0*p+u1*(12-2*p)+v0*p+v1*(14-p)
    compute_expected=13*h+14*u1+12*v1+(u0-u1)*p+(v0-2*v1)*r
    return_expected=13*h+12*u1+14*v1+(u0-2*u1+v0-v1)*p
    assert sp.expand(compute-compute_expected)==0
    assert sp.expand(return_rule-return_expected)==0
    return_slope=u0-2*u1+v0-v1
    identity_slope=u0-u1+v0-2*v1
    assert sp.expand(identity_slope-return_slope)==u1-v1
    both={u1:v1,v0:3*v1-u0}
    common=13*h+26*v1
    assert sp.expand(return_rule.subs(both)-common)==0
    assert sp.expand(compute.subs(both)-common-(u0-v1)*(p-r))==0
    for bit,A,B in family(1):
        for other,AA,BB in family(1):
            microscopic=sum(3**j*(h+u0*(A[0]//3**j%3)+u1*(A[1]//3**j%3)
                                 +v0*(BB[0]//3**j%3)+v1*(BB[1]//3**j%3)) for j in range(3))
            assert sp.expand(microscopic-compute.subs({p:A[0],r:BB[0]}))==0
        microscopic_return=sum(3**j*(h+u0*(B[0]//3**j%3)+u1*(B[1]//3**j%3)
                                    +v0*(A[0]//3**j%3)+v1*(A[1]//3**j%3)) for j in range(3))
        assert sp.expand(microscopic_return-return_rule.subs(p,A[0]))==0
    return dict(computation_increment=str(sp.expand(compute)),identity_return_increment=str(sp.expand(return_rule)),
                necessary_return_coefficient=str(return_slope),
                additional_identity_computation_coefficient=str(identity_slope),
                joint_specialization=dict(u1='v1',v0='3*v1-u0',common_increment=str(common)),
                scope='Necessary conditions only when the specified recoder handles every finite binary word under a uniform carry bound')


def contraction_checks():
    cases=admitted=0
    for b in range(-100,101):
        C=max(5,abs(b))
        L=1
        while 27**L<=26*C+abs(b):L+=1
        for initial in range(-C,C+1):
            c=initial;integral=True
            for _ in range(L):
                if (c+b)%27:
                    integral=False;break
                c=(c+b)//27
            if integral:
                assert 26*initial==b and c==initial
                admitted+=1
            cases+=1
    return dict(fixed_increment_initial_states=cases,integral_paths=admitted,
                increment_range=[-100,100],macro_base=27)


def verify():
    return dict(status='PASS_HIDDEN_BOOLEAN_CARRY_CONTEXTUAL_CODES',codes=code_checks(),
                finite_minimality=minimum_checks(),external=external_algebra(),
                contraction=contraction_checks(),
                scope='Exact physical code and scoped recoder conditions; code typing, ordinary input, phases and halting remain unpaid',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps(result,indent=2))
