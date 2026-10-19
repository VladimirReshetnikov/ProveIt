#!/usr/bin/env python3
"""Independent exact-rational validation of the affine certificates."""
from pathlib import Path
from fractions import Fraction as F
import collections,json,argparse
from independent_cfg import parse_source,build_cfg
ROOT=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser()
ap.add_argument("--source",type=Path,default=ROOT/"vendor/context246/sources/Prog254.v")
ap.add_argument("--inputs-dir",type=Path,default=ROOT/"experiments/audit_inputs")
ap.add_argument("--output",type=Path,default=ROOT/"results/audit/affine_audit.json")
args=ap.parse_args()
rows,leaves=parse_source(args.source)
successors,_=build_cfg(rows,leaves)
interval_data=json.loads((args.inputs_dir/"interval-invariants.json").read_text())
intervals=interval_data["invariants"]
initial=[3,0,0,0,3,0,0,0,0]
assert len(intervals)==len(leaves)==6460
assert all(z is None or (len(z)==9 and all(
    type(lo) is int and type(hi) is int and lo>=0 and (hi==9 or hi>=lo)
    for lo,hi in z)) for z in intervals)
def in_interval(x,bounds):
    return all(lo<=v and (hi==9 or v<=hi) for v,(lo,hi) in zip(x,bounds))
assert in_interval(initial,intervals[0])
def contained(a,b):
    return b is not None and all(bl<=al and (bh==9 or (ah!=9 and ah<=bh))
        for (al,ah),(bl,bh) in zip(a,b))
interval_edges=0
for i,(_,op,r) in enumerate(leaves):
    src=intervals[i]
    if src is None:continue
    branches=[]
    if op=="CI":
        image=[list(t) for t in src]
        lo,hi=image[r];image[r]=[lo+1,9 if hi==9 else hi+1]
        branches=[(successors[i][0],image)]
    elif op=="CD":
        lo,hi=src[r]
        if lo==0:
            image=[list(t) for t in src];image[r]=[0,0]
            branches.append((successors[i][0],image))
        if hi>0:
            image=[list(t) for t in src];image[r]=[max(lo,1)-1,9 if hi==9 else hi-1]
            branches.append((successors[i][1],image))
    else:branches=[(j,src) for j in successors[i]]
    for j,image in branches:
        # A computed finite upper endpoint9 must not be confused with infinity:
        # the stored source endpoint8+1 is9, and target9 meansinfinity; containment
        # above is conservatively valid in either interpretation.
        assert contained(image,intervals[j]),(i,j)
        interval_edges+=1
assert interval_edges==8384

def rref(vectors):
    a=[list(map(F,row)) for row in vectors if any(row)]
    k=0
    for c in range(10):
        j=next((j for j in range(k,len(a)) if a[j][c]),None)
        if j is None:continue
        a[k],a[j]=a[j],a[k]
        den=a[k][c];a[k]=[x/den for x in a[k]]
        for j in range(len(a)):
            if j!=k and a[j][c]:
                den=a[j][c];a[j]=[x-den*y for x,y in zip(a[j],a[k])]
        k+=1
    return a[:k]
def belongs(v,basis):
    v=list(map(F,v))
    for row in basis:
        p=next(i for i,x in enumerate(row) if x)
        a=v[p];v=[x-a*y for x,y in zip(v,row)]
    return not any(v)
def cut(basis,f):
    dot=[sum(x*y for x,y in zip(row,f)) for row in basis]
    j=next((j for j,v in enumerate(dot) if v),None)
    if j is None:return basis
    a=rref([[x-dot[k]/dot[j]*y for x,y in zip(row,basis[j])]
            for k,row in enumerate(basis) if k!=j])
    return a if any(row[-1] for row in a) else []
def eqs(basis):
    pivot={next(i for i,x in enumerate(row) if x):row for row in basis}
    result=[]
    for c in range(10):
        if c in pivot:continue
        f=[F(0)]*10;f[c]=F(1)
        for p,row in pivot.items():f[p]=-row[c]
        result.append(f)
    return result
def reduced_at(node,basis):
    if intervals[node] is None:return []
    for r,(lo,hi) in enumerate(intervals[node]):
        if lo==hi and hi!=9:
            f=[F(0)]*10;f[r]=F(1);f[-1]=-lo
            basis=cut(basis,f)
            if not basis:return []
    while basis:
        old=len(basis)
        for eq in eqs(basis):
            for sign in (1,-1):
                f=[sign*x for x in eq]
                if any(x<0 for x in f[:9]):continue
                lower=f[-1]+sum(f[r]*intervals[node][r][0] for r in range(9))
                if lower>0:return []
                if lower==0:
                    for r in range(9):
                        if f[r]:
                            g=[F(0)]*10;g[r]=F(1);g[-1]=-intervals[node][r][0]
                            basis=cut(basis,g)
                            if not basis:return []
        if len(basis)==old:return basis
    return basis
def shifted(basis,r,delta):
    return [[x+(delta*row[-1] if k==r else 0) for k,x in enumerate(row)] for row in basis]

results=[]
for reduced,name in ((False,"affine_invariant_certificate.json"),(True,"reduced_affine_certificate.json")):
    cert=json.loads((args.inputs_dir/name).read_text())
    assert len(cert["states"])==len(leaves)
    assert all(len(v)==10 for basis in cert["states"] for v in basis)
    bases=[rref(b) for b in cert["states"]]
    assert all(len(a)==len(b) for a,b in zip(bases,cert["states"]))
    assert all(not b or any(row[-1] for row in b) for b in bases)
    assert belongs(initial+[1],bases[0])
    edges=0;rejected=[]
    for i,(_,op,r) in enumerate(leaves):
        b=bases[i]
        if not b:continue
        if op=="CI":branches=[(successors[i][0],shifted(b,r,1),"increment")]
        elif op=="CD":
            f=[F(0)]*10;f[r]=F(1)
            zero=cut(b,f)
            pos=shifted(b,r,-1) if any(row[r] for row in b) else []
            if reduced and intervals[i][r][0]>0:zero=[]
            if reduced and intervals[i][r][1]==0:pos=[]
            branches=[(successors[i][1],pos,"positive"),(successors[i][0],zero,"zero")]
        else:branches=[(j,b,"control") for j in successors[i]]
        for j,image,kind in branches:
            if reduced:image=reduced_at(j,rref(image))
            if not image:rejected.append([i,kind])
            assert all(belongs(v,bases[j]) for v in image),(name,i,j,kind)
            edges+=1
    excluded=[i for i,b in enumerate(bases) if not b]
    assert excluded==cert["excluded_leaves"] and rejected==cert["excluded_guard_edges"]
    assert edges==cert["checked_edges"]
    results.append({"file":name,"status":"PASS","excluded_leaves":excluded,
                    "excluded_guard_edges":rejected,"checked_edge_obligations":edges})
result={"status":"PASS","independent_interval_edge_checks":interval_edges,"certificates":results,
        "method":"Own source parser/path arithmetic; Fraction Gaussian elimination and independent interval transfers.",
        "scope":"Inductiveness and listed exclusions; not exact reachability or a new exclusion beyond prior interval work."}
args.output.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))

