"""Non-mutating adapter for the audited bit-valued reference ScanComplex.

Not an adapter for the distinct optimized FastScan representation.
Requires an already valid differential; does not issue knot verdicts.
SPDX-License-Identifier: MIT-0
"""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[1]
if str(ROOT/'code') not in sys.path: sys.path.insert(0,str(ROOT/'code'))
from radical import Mat,Obj,survivor_profile

def predict_scancomplex(state):
    if not hasattr(state,'objects') or not hasattr(state,'out'):
        raise TypeError('expected reference ScanComplex objects/out interface')
    ids=list(state.objects); index={x:j for j,x in enumerate(ids)}
    types={}; descriptions=[]; obs=[]
    for x in ids:
        matching,h=state.objects[x]
        key=tuple(sorted(tuple(sorted(pair)) for pair in matching))
        if key not in types: types[key]=len(types); descriptions.append(key)
        obs.append(Obj(types[key],h))
    cols=[]
    for x,o in zip(ids,obs):
        col={}
        for y,f in state.out.get(x,{}).items():
            if type(f) is not int or f<0:
                raise TypeError('adapter requires bit-packed F2 morphisms')
            if y not in index: raise ValueError('differential targets missing object')
            i=index[y]
            if f&1 and obs[i].matching==o.matching: col[i]=1
        cols.append(col)
    obs=tuple(obs); profile=survivor_profile(Mat(obs,obs,cols))
    return {'objects_before':len(obs),'minimal_survivors':sum(profile.values()),
            'profile':[{'matching':[list(p) for p in descriptions[a]],'degree':h,'copies':n}
                       for (a,h),n in sorted(profile.items())]}
