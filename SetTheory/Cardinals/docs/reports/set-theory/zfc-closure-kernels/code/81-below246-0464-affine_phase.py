"""Exact rational affine-hull interpretation of the register-program CFG.

All soundness obligations are checked after convergence. The homogeneous
coordinate has index0. Zero guards intersect an affine subspace; positive
guards remove an identicallyzero register then translate by-1. Joins take
affine hulls. The finite zero/one/many invariant is an additional intersection.
"""
from fractions import Fraction as F
from collections import deque,Counter
from pathlib import Path
import sys,json,time
HERE=Path(__file__).parent
sys.path.insert(0,str(HERE.parent/'agent_logic'))
import audit_phase as P
N=10

def add(B,vector):
    v=list(vector)
    for i,row in B.items():
        x=v[i]
        if x:
            v=[a-x*b for a,b in zip(v,row)]
    try:p=next(i for i,x in enumerate(v) if x)
    except StopIteration:return B,False
    x=v[p];v=tuple(a/x for a in v)
    out={i:(tuple(a-row[p]*b for a,b in zip(row,v)) if row[p] else row) for i,row in B.items()}
    out[p]=v
    return dict(sorted(out.items())),True

def canon(rows):
    out={}
    for row in rows:out,_=add(out,row)
    return out

def intersect(B,r,value=0):
    coeff={i:row[r]-value*row[0] for i,row in B.items()}
    piv=next((i for i,x in coeff.items() if x),None)
    if piv is None:return B
    pivot=B[piv];scale=coeff[piv]
    rows=[]
    for i,row in B.items():
        if i==piv:continue
        factor=coeff[i]/scale
        rows.append(tuple(a-factor*b for a,b in zip(row,pivot)))
    out=canon(rows)
    return out if 0 in out else {}

def translate(B,r,k):
    rows=[]
    for row in B.values():
        row=list(row);row[r]+=k*row[0];rows.append(row)
    return canon(rows)

def transfer(B,leaf,positive):
    if not B:return {}
    _,op,r,_,_=leaf
    if op=='CI':return translate(B,r+1,1)
    if op=='CD':
        r+=1
        if not positive:return intersect(B,r)
        if all(row[r]==0 for row in B.values()):return {}
        # A constant register outside the positive naturals disables the edge.
        if all(i==0 or row[r]==0 for i,row in B.items()) and B[0][r]<1:return {}
        return translate(B,r,-1)
    return B

def reduced(B,mask):
    for r,bits in enumerate(mask,1):
        if bits in (1,2):B=intersect(B,r,int(bits==2))
    return B

def main():
    leaves,cases,by_leaf,first=P.read_program(P.PROGRAM.read_bytes())
    masks_result=P.analyze(leaves,cases,by_leaf,first,[4,1,1,1,4,1,1,1,1])
    masks=[masks_result['mask_classes'][i] if i is not None else None for i in masks_result['site_mask_class_ids']]
    B=[{} for _ in leaves]
    B[first]=canon([tuple(map(F,[1,3,0,0,0,3,0,0,0,0]))])
    queue=deque([first]);pending={first};pops=0;began=time.monotonic()
    while queue:
        i=queue.popleft();pending.discard(i);pops+=1
        for ci in by_leaf[i]:
            _,pos,j=cases[ci]
            if j is None:continue
            x=transfer(B[i],leaves[i],pos)
            if not x or masks[j] is None:continue
            x=reduced(x,masks[j])
            changed=False
            for v in x.values():
                B[j],update=add(B[j],v);changed|=update
            if changed and j not in pending:queue.append(j);pending.add(j)
        if pops%10000==0:print('progress',pops,'pending',len(queue),'seconds',time.monotonic()-began,flush=True)
    impossible=[]
    for c,(i,pos,j) in enumerate(cases):
        out=transfer(B[i],leaves[i],pos)
        if out and j is not None and masks[j] is not None:out=reduced(out,masks[j])
        if not out:impossible.append(c);continue
        if j is not None:
            for row in out.values():
                _,changed=add(B[j],row)
                assert not changed,(c,'failed postfix')
    rows={json.dumps({str(i):[str(x) for x in row] for i,row in b.items()},sort_keys=True) for b in B}
    classes=sorted(rows);indices={s:i for i,s in enumerate(classes)}
    answer=dict(status='PASS',seconds=time.monotonic()-began,pops=pops,impossible_cases=impossible,
        extra_exclusions=sorted(set(impossible)-set(masks_result['impossible_cases'])),
        affine_dimensions=dict(Counter(len(b)-1 for b in B)),all_postfix_checked=True,
        basis_classes=[json.loads(s) for s in classes],
        site_class_ids=[indices[json.dumps({str(i):[str(x) for x in row] for i,row in b.items()},sort_keys=True)] for b in B])
    (HERE/'affine_phase_result.json').write_text(json.dumps(answer,indent=2)+'\n')
    print(json.dumps({k:v for k,v in answer.items() if k not in ('basis_classes','site_class_ids')},indent=2),flush=True)

if __name__=='__main__':main()
