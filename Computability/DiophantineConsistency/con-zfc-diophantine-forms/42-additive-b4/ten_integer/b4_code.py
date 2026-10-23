"""Finite B4 code construction, exhaustive certificate, and coding circuit.

Bose-Chowla: logarithms of theta + GF(32) in GF(2^20)^*.
Only the explicit four-sum verification is needed by the adapter theorem.
"""
from itertools import combinations_with_replacement
from functools import lru_cache
from pathlib import Path
import hashlib
import json

MODULUS=(1<<20)|(1<<3)|1
ORDER=(1<<20)-1

def mul(x,y):
    r=0
    while y:
        if y&1:r^=x
        x<<=1
        if x>>20:x^=MODULUS
        y>>=1
    return r

def power(x,n):
    r=1
    while n:
        if n&1:r=mul(r,x)
        x=mul(x,x);n>>=1
    return r

def construct_code():
    assert power(2,ORDER)==1
    orders={p:power(2,ORDER//p) for p in (3,5,11,31,41)}
    assert all(x!=1 for x in orders.values())
    generator=power(2,ORDER//31)
    field=[0,1]
    for _ in range(1,31):field.append(mul(field[-1],generator))
    assert len(set(field))==32 and all(power(x,32)==x for x in field)
    targets={2^x for x in field}
    logs=[];x=1
    for j in range(ORDER):
        if x in targets:logs.append(j)
        x<<=1
        if x>>20:x^=MODULUS
    assert len(logs)==32
    gap,j=max(((logs[(j+1)%32]-logs[j])%ORDER,j) for j in range(32))
    origin=logs[(j+1)%32]
    weights=sorted((x-origin)%ORDER for x in logs)
    result=dict(field_modulus=MODULUS,primitive_element=2,group_order=ORDER,
                original_logs=logs,translation_origin=origin,weights=weights,
                max_weight=max(weights),four_sum_count=52360)
    check_code(result)
    return result

def check_code(code):
    weights=code['weights'];M=code['group_order']
    assert len(weights)==32 and weights[0]==0 and len(set(weights))==32
    assert weights==sorted(weights) and 0<weights[-1]<M
    seen={}
    for indices in combinations_with_replacement(range(32),4):
        s=sum(weights[i] for i in indices)
        assert s%M not in seen,(indices,seen.get(s%M))
        seen[s%M]=indices
    assert len(seen)==52360
    return {'four_multisets':len(seen),'distinct_residues':len(seen),
            'max_weight':weights[-1],'Lcode':4*weights[-1],
            'exhaustive_modular_injectivity':True}

def coding_blocks_b4(d,B,weights,keys):
    """D(B)=sum c_alpha B^(4T-alpha.weights); no divisions."""
    T=max(weights)
    powers=[d.power(B,T)]+[d.power(B,T-w) for w in weights]
    terms=[]
    for alpha,name in keys:
        assert alpha[0]==0 and len(alpha)==len(weights)+1
        ex=(4-sum(alpha),)+tuple(alpha[1:])
        co=d.const(name) if isinstance(name,int) else d.fixed(name)
        terms.append((ex,co))
    @lru_cache(None)
    def horner(ts):
        if not ts:return d.const(0)
        counts=[sum(ex[j]>0 for ex,co in ts) for j in range(len(powers))]
        if not max(counts):return d.plus(*(co for ex,co in ts))
        j=max(range(len(powers)),key=lambda j:(counts[j],sum(ex[j] for ex,co in ts),j))
        yes=[];no=[]
        for ex,co in ts:
            if ex[j]:
                ex=list(ex);ex[j]-=1;yes.append((tuple(ex),co))
            else:no.append((ex,co))
        return d.plus(horner(tuple(no)),d.times(powers[j],horner(tuple(yes))))
    Dcode=horner(tuple(terms))
    top=powers[0]
    return d.power(top,4),d.plus(*(d.power(B,w) for w in weights)),Dcode,top

if __name__=='__main__':
    code=construct_code()
    path=Path(__file__).with_name('bose_chowla32.json')
    if path.exists():assert json.loads(path.read_text())==code
    else:path.write_text(json.dumps(code,indent=2)+'\n')
    print(json.dumps(check_code(code),indent=2))
