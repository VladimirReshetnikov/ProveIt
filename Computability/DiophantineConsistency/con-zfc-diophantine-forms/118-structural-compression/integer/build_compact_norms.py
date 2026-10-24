"""Reuse the retained 28-operation norm with shared denominator scaling.

The norm schedule is from the pinned positive endpoint's ORIGINAL_PROOF.md,
Section 1. The new contribution here is its exact adapter to the current
integer parent circuits, including common delta*scale^2 sharing.
"""
import json
from pathlib import Path
from collections import Counter
HERE=Path(__file__).resolve().parent

def build(kind):
    if kind=='trace13':
        pname='trace13_parent.json';start=116;Z=115;scale2=108;delta=67
        df,dt,dg,cy=65,79,105,74;weights=(1,1,1);rational=True
    else:
        variant=kind.split('_',1)[1]
        pname=f'scalar12_{variant}_parent.json';start=125;Z=124;scale2=112;delta=88
        df,dt,dg,cy=86,102,80,97;weights=(9,81,729);rational=variant=='rational'
    parent=json.loads((HERE/pname).read_text());out=dict(parent)
    nodes=[list(n) for n in parent['nodes'][:start]]
    leaves={n[1]:i for i,n in enumerate(nodes) if n[0]=='integer'}
    def c(k):
        if k not in leaves:leaves[k]=len(nodes);nodes.append(['integer',k])
        return leaves[k]
    def op(kind,a,b):nodes.append([kind,a,b]);return len(nodes)-1
    def add(a,b):return op('add',a,b)
    def sub(a,b):return op('sub',a,b)
    def mul(a,b):return op('mul',a,b)
    def sq(a):return mul(a,a)
    z=sq(Z)
    if rational:
        z=mul(delta,z);common=mul(delta,scale2);d=mul(scale2,cy)
    else:
        common=scale2;d=mul(mul(scale2,delta),cy)
    rad=[]
    for source,weight in zip((df,dt,dg),weights):
        factor=common if weight==1 else mul(common,c(weight))
        rad.append(mul(factor,source))
    a,b,e=rad
    ab_sum=add(a,b);ab=mul(a,b)
    sig1=add(ab_sum,e);sig2=add(ab,mul(ab_sum,e));sig3=mul(ab,e)
    U=add(z,d);Po=sub(U,sig1);Po2=sq(Po);sd=mul(z,d)
    Pe=add(Po2,mul(c(4),sub(sd,sig2)))
    Ge=add(sq(Pe),mul(c(16),sub(mul(sd,Po2),mul(c(4),mul(sig3,U)))))
    Go=sub(mul(Pe,Po),mul(c(16),sig3))
    final=sub(sq(Ge),mul(c(64),mul(sd,sq(Go))))
    out['nodes']=nodes;out['output']=final
    out['named_registers']={k:v for k,v in parent['named_registers'].items() if v<start}
    out['named_registers'].update({'output':final,'norm_sig1':sig1,'norm_sig2':sig2,'norm_sig3':sig3,'norm_Pe':Pe,'norm_Po':Po,'norm_Ge':Ge,'norm_Go':Go})
    counts=Counter(n[0] for n in nodes if n[0] in ('add','sub','mul'))
    out['operation_counts']=dict(sorted(counts.items()));out['operations']=sum(counts.values())
    out['name']=f'integer_compact_{kind}'
    out['proof']='COMPACT_NORM_ADDENDUM.md; identical polynomial to the pinned integer parent.'
    if 'ordinary_proof' in out:out['ordinary_proof']=out['proof']
    path=HERE/f'compact_{kind}.json';path.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    return {'file':path.name,'operations':out['operations'],'operation_counts':out['operation_counts'],'degree':out['exact_degree']}

if __name__=='__main__':print(json.dumps([build(k) for k in ('trace13','scalar12_rational','scalar12_integral')],indent=2))
