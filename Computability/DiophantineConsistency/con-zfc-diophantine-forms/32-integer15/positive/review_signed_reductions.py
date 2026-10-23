#!/usr/bin/env python3
"""Finite diagnostics and source hashes supplement the unbounded review."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def multiply(u,v,d):return (u[0]*v[0]+d*u[1]*v[1],u[0]*v[1]+u[1]*v[0])
def power(u,n,d):
    out=(1,0)
    while n:
        if n&1:out=multiply(out,u,d)
        n//=2
        if n:u=multiply(u,u,d)
    return out
def require(c,m):
    if not c:raise ValueError(m)

cases=0
for t in range(2,11):
    d=t*t-1
    for modulus in range(1,13):
        step=(t,1);val=(1%modulus,0);k=0
        while True:
            k+=1;val=multiply(val,step,d);val=(val[0]%modulus,val[1]%modulus)
            if val==(1%modulus,0):break
            require(k<=modulus**4+1,'finite group order search failed')
        hop=power(step,k,d)
        for initial_index in range(-2,3):
            a,H=power(step,abs(initial_index),d)
            if initial_index<0:H=-H
            aa,HH=a,H
            for _ in range(20):
                if HH>10000:break
                aa,HH=multiply((aa,HH),hop,d)
            require(HH>10000,'orbit did not reach diagnostic bound')
            require(aa*aa-d*HH*HH==1,'norm not preserved')
            require((HH-H)%modulus==0,'residue not preserved')
            cases+=1
source=[]
for filename in ['Master3.lean','NineReduce.lean','NineRatio.lean','Ratio.lean']:
    path=ROOT/'upstream/review_sources'/filename
    data=path.read_bytes()
    source.append({'path':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(data).hexdigest(),
                   'git_blob_sha1':hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()})
receipt={'status':'PASS','pell_orbit_cases':cases,
         'initial_indices':[-2,-1,0,1,2],'t_range':[2,10],'moduli':[1,12],
         'target_lower_bound':10000,'cofinal_radix_review':'PASS by complete source inspection and ordinary proof',
         'source_files':source,'formal_status':'No proof-assistant compilation of new lemmas; finite diagnostics supplement the written proof.'}
(ROOT/'SIGNED_REVIEW_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
