#!/usr/bin/env python3
"""Fixed-table, bounded deterministic control histories; no counter branches."""
from itertools import product
from pathlib import Path
import json
import sympy as sp
import explore_base_three_pell_kernel as kernel
import round4_1980_operation_count as baseline
from round13_1980_certificate import verify_primitives


def constants(successors,initial,final):
    # A phase bit removes self-loops without changing the original program.
    n=len(successors);f=[2*successors[i//2]+1-i%2 for i in range(2*n)]
    a=[3**i for i in range(2*n)];d=max(a);g=3**d
    S=sum(3**j for j in a)
    positions=[d+a[f[i]]-a[i] for i in range(2*n)]
    assert len(set(positions))==len(positions) and min(positions)>=0
    K=sum(3**j for j in positions)
    B=2;W=9
    while W<=max(K*S,g*S,2*S+1):B+=2;W*=9
    return dict(f=f,a=a,d=d,g=g,S=S,K=K,B=B,W=W,
                initial=initial,final=final,initial_word=3**a[initial],final_word=3**a[final])


PROGRAM=constants([1,1],0,2)
OUTER_NAMES=['H','Rep','C','V','TestC','TestV','alpha']
NAMES=['q']+OUTER_NAMES+kernel.CORE_NAMES
SYM={x:sp.Symbol(x) for x in NAMES}


def build(c=PROGRAM):
    W,S,K,g,I,F=[c[x] for x in ['W','S','K','g','initial_word','final_word']]
    ops=[
        ('qm1','*',W-1,'H'),('q_rhs','+','qm1',1),
        ('rep_rhs','*',(W-1)//2,'H'),
        ('SH','*',S,'H'),('input_lhs','+','C','Rep'),('input_rhs','+','SH','TestC'),
        ('gSH','*',g*S,'H'),('junk_lhs','+','V','gSH'),
        ('routing_product','*',W*K-g,'C'),('routing_lhs','+','routing_product',g*I),
        ('final_product','*',g*F,'q'),('junk_product','*',W,'V'),
        ('routing_rhs','+','final_product','junk_product'),
        ('pair_sum','+','TestC','TestV'),('bound_lhs','+','pair_sum','alpha'),
        ('pack0','*','q','TestV'),('pack1','+','TestC','pack0'),
        ('pack2','*','q','pack1'),('pack3','+','V','pack2'),
        ('pack4','*','q','pack3'),('P0','+','C','pack4'),
    ]+kernel.OUTER+kernel.CORE
    tests=[('q','q_rhs'),('Rep','rep_rhs'),('input_lhs','input_rhs'),
           ('junk_lhs','TestV'),('routing_lhs','routing_rhs'),('bound_lhs','q')]+kernel.EQUALITIES
    z=SYM;q,H,Rep,C,V,TC,TV,alpha=[z[x] for x in ['q']+OUTER_NAMES]
    P0=C+q*V+q*q*TC+q**3*TV
    source=[q-(W-1)*H-1,Rep-(W-1)*H/2,C+Rep-S*H-TC,
            V+g*S*H-TV,(W*K-g)*C+g*I-g*F*q-W*V,TC+TV+alpha-q]
    sub={kernel.SYM[x]:z[x] for x in kernel.CORE_NAMES}
    sub.update({kernel.SYM['q']:q,kernel.SYM['P0']:P0})
    source.extend(p.subs(sub,simultaneous=True) for p in kernel.source_residuals())
    return ops,tests,source


def certificate():
    ops,tests,source=build();env=dict(SYM)
    histogram=baseline.run_schedule(ops,env)
    correction=source[-3]*((2*SYM['r']+1+SYM['j']*SYM['c'])**2-SYM['y_aux']**2)
    records=[]
    for index,((left,right),p) in enumerate(zip(tests,source)):
        extra=correction if index==len(source)-2 else sp.Integer(0)
        assert sp.expand(env[left]-env[right]-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(p)))
    primitive,counts=verify_primitives(ops,env)
    assert len(primitive)==70 and counts=={'+':31,'*':39}
    assert len(tests)==len(source)==17
    return dict(operations=70,primitive_histogram=counts,histogram=histogram,
                parameters=['q'],positive_unknowns=OUTER_NAMES+kernel.CORE_NAMES,
                equations=17,instructions=primitive,residuals=records,
                program=PROGRAM)


def boolean(value):
    if value<0:return False
    while value:
        value,d=divmod(value,3)
        if d>1:return False
    return True


def v3central(value):
    other=2*value;result=0
    while other:
        value//=3;other//=3;result+=other-2*value
    return result


def canonical(c,height,start=None):
    W,S,g,K=[c[x] for x in ['W','S','g','K']]
    state=c['initial'] if start is None else start
    rows=[];nextrows=[]
    for _ in range(height):
        rows.append(3**c['a'][state]);state=c['f'][state]
        nextrows.append(3**c['a'][state])
    q=W**height;H=(q-1)//(W-1);Rep=(q-1)//2
    C=sum(row*W**j for j,row in enumerate(rows))
    Next=sum(row*W**j for j,row in enumerate(nextrows));V=K*C-g*Next
    TC=C+Rep-S*H;TV=V+g*S*H;alpha=q-TC-TV
    assert min(C,V,TC,TV,H,Rep,alpha)>0
    assert all(boolean(x) and x<q for x in [C,V,TC,TV])
    assert (W*K-g)*C+g*rows[0]==g*nextrows[-1]*q+W*V
    packed=C+q*V+q*q*TC+q**3*TV
    assert packed%2==0 and packed<q**4 and boolean(packed)
    r=9*q**4-3*packed-1
    assert r%2==0 and v3central(r)==4*c['B']*height+2
    return state


def regression():
    coefficient_cases=canonical_cases=raw_candidates=accepted=0
    # Exhaust every fixed successor map on two and three original states.
    for n in [2,3]:
        for successors in product(range(n),repeat=n):
            c=constants(successors,0,0);f,a,d=c['f'],c['a'],c['d']
            for i,j in product(range(2*n),repeat=2):
                hits=sum(a[i]+d+a[f[k]]-a[k]==d+a[j] for k in range(2*n))
                assert hits==int(f[i]==j)
                coefficient_cases+=1
            if n==2:
                for initial,height in product(range(4),range(1,7)):
                    end=canonical(c,height,initial)
                    cur=initial
                    for _ in range(height):cur=f[cur]
                    assert end==cur;canonical_cases+=1
    # At fixed two-row extent enumerate all source-support subsets, not only
    # one-hot histories; solve the merged routing equation and test the mask.
    for successors in product(range(2),repeat=2):
        for initial,final in product(range(4),repeat=2):
            c=constants(successors,initial,final)
            W,S,K,g,I,F=[c[x] for x in ['W','S','K','g','initial_word','final_word']]
            q=W*W;H=W+1;Rep=(q-1)//2
            possible=[sum(3**c['a'][i] for i in range(4) if bits>>i&1) for bits in range(16)]
            for low,high in product(possible,repeat=2):
                raw_candidates+=1;C=low+W*high
                numerator=(W*K-g)*C+g*I-g*F*q
                V,remainder=divmod(numerator,W)
                if remainder or C<=0 or V<=0:continue
                TC=C+Rep-S*H;TV=V+g*S*H;alpha=q-TC-TV
                if min(TC,TV,alpha)<=0:continue
                packed=C+q*V+q*q*TC+q**3*TV
                assert 0<packed<q**4
                r=9*q**4-3*packed-1
                if v3central(r)<8*c['B']+2:continue
                accepted+=1
                assert low==I and high==3**c['a'][c['f'][initial]]
                assert c['f'][c['f'][initial]]==final
    assert accepted==16
    return dict(exact_target_coefficients=coefficient_cases,canonical_histories=canonical_cases,
                arbitrary_source_subset_histories=raw_candidates,accepted_complete_candidates=accepted,
                scope='All fixed maps on2/3 original states for target coefficients, canonical two-state histories, and all two-row source-support subsets for2-state maps. Full outer masks evaluated by independent factorial valuation; huge Pell tuples are not instantiated.')


def verify():
    return dict(status='PASS_FIXED_PROGRAM_ROUTING_COMPONENT',arithmetic=certificate(),
                regression=regression(),proof='../1980/EXPLORATION_FIXED_PROGRAM_ROUTING.md',
                scope='Exact deterministic finite-graph histories with a fixed program table and fixed endpoints. Counter-dependent branch selection, register selection, zero tests, raw input and universal acceptance remain unpaid.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print(result['regression'])
