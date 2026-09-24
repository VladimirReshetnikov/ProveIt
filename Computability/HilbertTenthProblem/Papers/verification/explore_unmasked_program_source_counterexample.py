#!/usr/bin/env python3
"""Exact scoped counterexample: omit the fixed router's source-word mask."""
from pathlib import Path
import json
import sympy as sp
import explore_nondeterministic_program_routing as old


SYM=old.base.SYM
CORE_NAMES=old.base.kernel.CORE_NAMES
A=[8,10,14]
EDGES=[(0,1),(1,2)]
D=14
POSITIONS=[D+A[j]-A[i] for i,j in EDGES]+[D-ai for ai in A]
PROGRAM=dict(m=3,edges=EDGES,a=A,d=D,spacing=2,positions=POSITIONS,
    S=sum(3**e for e in A),g=3**D,K=sum(3**e for e in POSITIONS),
    forbidden=3**(D+1),B=34,W=3**34,initial=0,final=0,
    initial_word=3**A[0],final_word=3**A[0])
SOURCE_WORD=28871726544739970418459818800067147328666199790815308
JUNK_WORD=12282797154274314089309142195079934980011510335861921202065040


def kernel_source(scale,packed):
    z=SYM
    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y=[z[n] for n in CORE_NAMES]
    U,Y=w*scale,s*scale;Q=U*Y**2;disc=a*a+6*a+8;u=2*r+1+j*c
    return [r-scale+3*packed+1,Q*(Q+1)*k*k-tau*(tau+1),c-Y*k-eta,
            k-eta-zeta,k-r-1-h*U*Y,a-Y*(U+1),d-U-a*c-ga*(6*a+8),
            d*d-disc*c*c-1,(i*c*c)**2-disc*(f*f-1),
            disc*(f*f-1)*(u*u-y*y)-(1-y*y),u-c-o*f]


def build():
    prior_ops,pairs,prior_source=old.build(PROGRAM)
    packing=[('pack0','*','q','TestV'),('pack1','+','TestC','pack0'),
             ('pack2','*','q','pack1'),('P0','+','V','pack2')]
    ops=[];inserted=False
    for name,op,left,right in prior_ops:
        if name.startswith('pack') or name=='P0':
            if not inserted:ops.extend(packing);inserted=True
            continue
        if name=='L':right='q'
        ops.append((name,op,left,right))
    q=SYM['q'];packed=SYM['V']+q*SYM['TestC']+q*q*SYM['TestV']
    return ops,pairs,prior_source[:5]+kernel_source(9*q**3,packed)


def verify_certificate():
    ops,pairs,source=build();env=dict(SYM);hist=old.base.baseline.run_schedule(ops,env)
    correction=source[-3]*((2*SYM['r']+1+SYM['j']*SYM['c'])**2-SYM['y_aux']**2)
    records=[]
    for index,((left,right),p) in enumerate(zip(pairs,source)):
        extra=correction if index==len(source)-2 else 0
        assert sp.expand(env[left]-env[right]-p-extra)==0,index
        records.append(dict(index=index,equality=[left,right],source=sp.sstr(p),correction=sp.sstr(extra)))
    primitive,counts=old.base.verify_primitives(ops,env)
    assert len(primitive)==66 and counts=={'+':29,'*':37} and len(source)==16
    return dict(status='ARITHMETIC_PASS_SEMANTIC_COUNTEREXAMPLE',operations=66,primitive_histogram=counts,
                histogram=hist,parameters=['q'],positive_unknowns=old.base.OUTER_NAMES+CORE_NAMES,
                equations=16,primitive_instructions=primitive,residuals=records,
                masked_fields=['V','TestC','TestV'],program=PROGRAM,
                scope='Fixed-router omission only. This is not the eleven-field cyclic118 controller/counter omission.')


def verify_counterexample():
    c=PROGRAM;R=c['W'];q=R**4;H=(q-1)//(R-1);J=(q-1)//2
    C=SOURCE_WORD;V=JUNK_WORD;TC=C+J-c['S']*H;TV=V+c['forbidden']*H;alpha=q-TC-TV
    z=dict(q=q,H=H,C=C,V=V,TestC=TC,TestV=TV,alpha=alpha)
    assert min(z.values())>0
    assert R>max((c['K']+c['g'])*c['S'],2*c['S']+1,c['forbidden'])
    assert len({A[i]+A[j] for i in range(3) for j in range(i,3)})==6
    assert 2*min(A)>max(A) and len(POSITIONS)==len(set(POSITIONS))
    assert all(old.base.old.boolean(v) and v<q for v in (V,TC,TV))
    assert not old.base.old.boolean(C) and C%2==0
    source=build()[2];sub={SYM[n]:v for n,v in z.items()}
    assert all(source[i].subs(sub,simultaneous=True)==0 for i in range(5))
    P=V+q*TC+q*q*TV;scale=9*q**3;r=scale-3*P-1
    assert 0<P<q**3 and old.base.old.boolean(P) and P%2==0 and r%2==0
    assert old.base.old.v3central(r)==410
    n0=3**205
    assert n0*n0==scale and n0<=r<2*n0**3 and scale<r*r
    # The actual graph is acyclic, so it has no positive return to0 at all.
    reachable={0}
    for _ in range(4):reachable={j for i,j in EDGES if i in reachable}
    assert 0 not in reachable and reachable==set()
    return dict(height=4,outer_values={name:str(v) for name,v in z.items()},
                packed=str(P),index=str(r),scale=str(scale),valuation=410,even_index=True,
                outer_residuals=5,masked_field_count=3,source_word_boolean=False,
                true_graph_endpoints_at_height4=sorted(reachable),
                full_positive_extension='Actual scale9q3=3^410 has integer square root3^205. The even index and all original base-three43 positive-converse growth/divisibility hypotheses hold, so all17 positive Pell auxiliaries exist. They are not instantiated numerically.')


def verify():
    return dict(status='REFUTED_UNMASKED_FIXED_ROUTER_SOURCE_66',arithmetic=verify_certificate(),
                counterexample=verify_counterexample(),
                proof='../1980/EXPLORATION_UNMASKED_PROGRAM_SOURCE.md',
                full_cyclic_counter_omission='OPEN: this fixed-router false positive has not been extended through the typed sign/zero projections and raw numerical counter equations.')


if __name__=='__main__':
    result=verify();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status']);print(result['arithmetic']['operations'],result['arithmetic']['primitive_histogram'])
    print({k:v for k,v in result['counterexample'].items() if k not in ('outer_values','packed','index','scale')})
