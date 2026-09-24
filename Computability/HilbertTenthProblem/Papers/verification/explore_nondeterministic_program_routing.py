#!/usr/bin/env python3
"""Exact68 fixed directed-graph histories with a paid one-head marker."""
from collections import Counter
from itertools import product
from pathlib import Path
import json
import sympy as sp

import explore_permutation_program_routing as base


def constants(m,edges,initial=0,final=0):
    edges=sorted(set(edges))
    assert m>=2 and all(0<=i<m and 0<=j<m and i!=j for i,j in edges)
    spacing=2
    while 3**spacing<=m or (spacing-1-m)%2:spacing+=1
    a=[spacing*3**i for i in range(m)];d=max(a)
    positions=[d+a[j]-a[i] for i,j in edges]+[d-a[i] for i in range(m)]
    assert len(positions)==len(set(positions)) and min(positions)>=0
    S=sum(3**e for e in a);g=3**d;K=sum(3**e for e in positions)
    forbidden=sum(3**(d+h) for h in range(1,spacing))
    B=2;W=9
    while W<=max(K*S,g*S,2*S+1,forbidden):B+=2;W*=9
    return dict(m=m,edges=edges,a=a,d=d,spacing=spacing,positions=positions,
                S=S,g=g,K=K,forbidden=forbidden,B=B,W=W,
                initial=initial,final=final,initial_word=3**a[initial],final_word=3**a[final])


PROGRAM=constants(3,[(0,1),(0,2),(1,2),(2,0)],0,2)


def build(c=PROGRAM):
    ops,tests,source=base.build(c,permutation=False)
    ops=[(name,op,c['forbidden'] if name=='gSH' else left,right) for name,op,left,right in ops]
    z=base.SYM
    source[2]=z['V']+c['forbidden']*z['H']-z['TestV']
    return ops,tests,source


def certificate():
    ops,tests,source=build();env=dict(base.SYM)
    hist=base.baseline.run_schedule(ops,env)
    correction=source[-3]*((2*env['r']+1+env['j']*env['c'])**2-env['y_aux']**2)
    records=[]
    for index,((left,right),p) in enumerate(zip(tests,source)):
        extra=correction if index==len(source)-2 else 0
        assert sp.expand(env[left]-env[right]-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(extra)))
    primitive,counts=base.verify_primitives(ops,env)
    assert len(primitive)==68 and counts=={'+':30,'*':38} and len(tests)==len(source)==16
    assert len(base.OUTER_NAMES+base.kernel.CORE_NAMES)==23
    return dict(operations=68,primitive_histogram=counts,histogram=hist,parameters=['q'],
                positive_unknowns=base.OUTER_NAMES+base.kernel.CORE_NAMES,equations=16,
                instructions=primitive,residuals=records,program=PROGRAM,
                masked_fields=['C','V','TestC','TestV'])


def subset_words(c):
    return [sum(3**c['a'][i] for i in range(c['m']) if mask>>i&1) for mask in range(1<<c['m'])]


def coefficient_checks(c):
    count=0;m=c['m'];a=c['a'];d=c['d'];spacing=c['spacing']
    for mask,word in enumerate(subset_words(c)):
        coeff=Counter(e+a[i] for e in c['positions'] for i in range(m) if mask>>i&1)
        assert max(coeff.values(),default=0)<=m<3**spacing
        assert all(e%spacing==0 for e in coeff)
        value=c['K']*word
        assert value<c['W']
        assert coeff[d]==mask.bit_count()
        assert value//3**d%(3**spacing)==mask.bit_count()
        count+=1
        for j in range(m):
            expected=sum(bool(mask>>i&1) for i,target in c['edges'] if target==j)
            assert coeff[d+a[j]]==expected
            assert value//3**(d+a[j])%(3**spacing)==expected
            count+=1
    return count


def canonical(c,path):
    assert len(path)>=2 and all((i,j) in c['edges'] for i,j in zip(path,path[1:]))
    height=len(path)-1;W,S,K,g,Fmask=[c[n] for n in ['W','S','K','g','forbidden']]
    q=W**height;H=(q-1)//(W-1);Rep=(q-1)//2
    C=sum(3**c['a'][state]*W**t for t,state in enumerate(path[:-1]))
    Next=sum(3**c['a'][state]*W**t for t,state in enumerate(path[1:]))
    V=K*C-g*Next;TC=C+Rep-S*H;TV=V+Fmask*H;alpha=q-TC-TV
    assert min(H,C,V,TC,TV,alpha)>0
    assert all(base.old.boolean(value) and value<q for value in (C,V,TC,TV))
    I=3**c['a'][path[0]];F=3**c['a'][path[-1]]
    assert (W*K-g)*C+g*I==g*F*q+W*V
    packed=C+q*V+q*q*TC+q**3*TV
    assert packed%2==0 and 0<packed<q**4 and base.old.boolean(packed)
    r=9*q**4-3*packed-1
    assert r%2==0 and base.old.v3central(r)==4*c['B']*height+2


def regression():
    tables=coefficient_cases=canonical_cases=candidates=accepted=0
    sample_paths=[]
    for m in (2,3):
        possible_edges=[(i,j) for i in range(m) for j in range(m) if i!=j]
        for bits in range(1<<len(possible_edges)):
            edges=[edge for h,edge in enumerate(possible_edges) if bits>>h&1]
            c=constants(m,edges);tables+=1;coefficient_cases+=coefficient_checks(c)
            for height in range(1,4):
                for path in product(range(m),repeat=height+1):
                    if all((i,j) in edges for i,j in zip(path,path[1:])):
                        canonical(c,path);canonical_cases+=1
            W,S,K,g,Fmask=[c[n] for n in ['W','S','K','g','forbidden']]
            q=W*W;H=W+1;Rep=(q-1)//2;words=subset_words(c)
            for initial,final in product(range(m),repeat=2):
                I=3**c['a'][initial];F=3**c['a'][final]
                for low,high in product(words,repeat=2):
                    candidates+=1;C=low+W*high
                    numerator=(W*K-g)*C+g*I-g*F*q
                    V,remainder=divmod(numerator,W)
                    if remainder or C<=0 or V<=0:continue
                    TC=C+Rep-S*H;TV=V+Fmask*H;alpha=q-TC-TV
                    if min(TC,TV,alpha)<=0:continue
                    assert max(C,V,TC,TV)<q
                    packed=C+q*V+q*q*TC+q**3*TV
                    assert 0<packed<q**4
                    r=9*q**4-3*packed-1
                    if base.old.v3central(r)<8*c['B']+2:continue
                    accepted+=1
                    assert low==I
                    middle=[i for i in range(m) if high==3**c['a'][i]]
                    assert len(middle)==1 and (initial,middle[0]) in edges and (middle[0],final) in edges
                    if len(sample_paths)<8:sample_paths.append(dict(edges=edges,path=[initial,middle[0],final]))
    return dict(loop_free_graph_tables=tables,normalized_marker_and_target_checks=coefficient_cases,
                canonical_histories=canonical_cases,arbitrary_subset_histories=candidates,
                accepted_complete_candidates=accepted,sample_paths=sample_paths,
                scope='Every loop-free graph on2/3 states, every source subset for coefficient tests, canonical paths of lengths1..3, all two-row source-subset tuples and endpoints. Acceptance uses the independent factorial valuation, without a one-head or chosen-edge filter.')


def verify():
    return dict(status='PASS_NONDETERMINISTIC_FIXED_GRAPH_ROUTING',arithmetic=certificate(),
                regression=regression(),proof='../1980/EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md',
                scope='Fixed finite directed-graph paths only. Typed counter projections, zero tests, variable row geometry, raw counter composition and universal acceptance are not included in68.')


if __name__=='__main__':
    result=verify()
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print({k:v for k,v in result['regression'].items() if k!='sample_paths'})
