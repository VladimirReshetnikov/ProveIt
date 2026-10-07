#!/usr/bin/env python3
"""Direct exact small-distance checks, independent of the large set enumeration.
Run after verify.py. Uses only the standard library and the supplied verify module.
"""
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json
from verify import group,cube_vertices,pdelta,poly,full_weighted_check

def cube_count(mods,a):
    _,add,_=group(mods);h=len(a)
    return sum(product_value(a,cube_vertices(add,x,u,v,w))
               for x,u,v,w in product(range(h),repeat=4))

def product_value(a,indices):
    out=Q(1)
    for i in indices:out*=a[i]
    return out

def run():
    records=[]
    cases=[
        ((6,), [Q(99,100),Q(1,400),Q(199,200),Q(0),Q(1),Q(0)], [0,2,4]),
        ((9,), [Q(99,100),Q(1,500),Q(0),Q(199,200),Q(0),Q(0),Q(1),Q(0),Q(0)], [0,3,6]),
        ((4,), [Q(199,200),Q(1,1000),Q(199,200),Q(0)], [0,2]),
        ((3,), [Q(999,1000)]*3, [0,1,2]),
    ]
    for mods,a,H in cases:
        n=sum(a);r=sum(1-a[i] for i in H);s=sum(a[i] for i in range(len(a)) if i not in H)
        delta=(r+s)/n; eps=1-cube_count(mods,a)/n**4
        assert delta<=Q(1,50)
        # All H here are cyclic, ordered by their natural generator.
        holes=full_weighted_check((len(H),),[1-a[i] for i in H])
        e=Q(holes['energy_defect']);B=Q(holes['parity']);W=Q(holes['remainder'])
        bound=pdelta(delta)+Q(7,2)*delta*s/n+((12*len(H)-35*r)*e+W-2*B)/n**4
        assert eps>=bound
        if B==0: assert eps>=pdelta(delta)
        records.append({'group':list(mods),'H_indices':H,'weights':list(map(str,a)),
                        'delta':str(delta),'epsilon':str(eps),'refined_lower_bound':str(bound),
                        'slack':str(eps-bound)})
    # Independent O(q^2) derivative count for the local equality at q=51.
    # C3(A) = sum_t E(A intersect (A-t)); compute each energy by correlations.
    q=51;A=set(range(1,q));C=0
    for t in range(q):
        B={x for x in A if (x+t)%q in A}
        C+=sum(sum(x in B and (x+u)%q in B for x in range(q))**2 for u in range(q))
    assert C==5774600
    assert 1-Q(C,50**4)==pdelta(Q(1,50))
    report={'status':'all exact local checks passed','weighted_local_cases':records,
            'independent_cyclic_equality':{'q':q,'cube_count':C,'epsilon':str(1-Q(C,50**4))}}
    Path(__file__).with_name('local_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print('4 local weighted checks and the Z/51Z exact equality passed.')

if __name__=='__main__':run()
