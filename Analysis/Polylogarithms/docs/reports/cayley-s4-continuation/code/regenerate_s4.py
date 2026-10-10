#!/usr/bin/env python3
"""Optional exact certificate search; not part of the trusted verifier.

Generate all prescribed weight-(1,4)/(2,3) double-shuffle rows, adjoin one
Cayley row, and use fraction-free sparse elimination. Output is checked
with the ordinary independent verifiers. No external dependency.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from itertools import product
from math import gcd
from pathlib import Path
import argparse,json,time
from word_algebra import *
from verify_s4 import verify
from verify_s4_independent import verify as verify_other

def candidates():
    def words(n):return [w for w in product(range(-1,4),repeat=n) if admissible(w)]
    rows=[];names=[];seen=set()
    for p in [1,2]:
        us=words(p)+([(0,)] if p==1 else [])
        for u in us:
            for v in words(5-p):
                row=odd_projection(double_shuffle(u,v))
                if not row:continue
                g=0
                for c in row.values():g=gcd(g,c)
                if row[min(row)]<0:g=-g
                row={w:c//g for w,c in row.items()}
                key=tuple(sorted(row.items()))
                if key not in seen:
                    seen.add(key);rows.append(row);names.append((u,v,g))
    A=(-1,-1,-1,1,1)
    rows.append(odd_projection(plus({A:1},cayley(A),-1)))
    names.append(('cayley',A))
    target0=odd_projection(target())
    columns=sorted(set().union(target0,*(r.keys() for r in rows)),
                   key=lambda w:(-sum(a!=-1 for a in w),w))
    return rows,names,target0,columns

def eliminate(rows,target0,columns):
    ci={w:j for j,w in enumerate(columns)};nr=len(rows);T=nr
    R={i:{ci[w]:c for w,c in r.items()} for i,r in enumerate(rows+[target0])}
    incidence=[set() for _ in columns]
    for i,r in R.items():
        for j in r:incidence[j].add(i)
    nodes=[];node_id={i:i for i in R};leaves=len(R);rank=0
    while R[T]:
        best=None
        for i,r in R.items():
            if i==T or not r:continue
            j=min(r,key=lambda j:(len(incidence[j]),abs(r[j]).bit_length(),j))
            key=((len(r)-1)*(len(incidence[j])-1),
                 max(abs(c).bit_length() for c in r.values()),len(r)+len(incidence[j]),i,j)
            if best is None or key<best:best=key
        if best is None:raise ArithmeticError('Target is not in this row span')
        *_,i,j=best;pivot=R[i];b=pivot[j];pivot_node=node_id[i]
        for k in list(incidence[j]-{i}):
            r=R[k];a=r[j];g=gcd(a,b);aa=a//g;bb=b//g
            z={h:c*bb for h,c in r.items()}
            for h,c in pivot.items():z[h]=z.get(h,0)-aa*c
            z={h:c for h,c in z.items() if c};divisor=0
            for c in z.values():divisor=gcd(divisor,c)
            divisor=divisor or 1
            if z and z[min(z)]<0:divisor=-divisor
            z={h:c//divisor for h,c in z.items()}
            for h in r.keys()-z.keys():incidence[h].discard(k)
            for h in z.keys()-r.keys():incidence[h].add(k)
            nodes.append((node_id[k],pivot_node,bb,aa,divisor))
            node_id[k]=leaves+len(nodes)-1;R[k]=z
        for h in pivot:incidence[h].discard(i)
        del R[i];rank+=1
    # Reverse the elimination DAG to recover a rational row certificate.
    weights=defaultdict(Q);weights[node_id[T]]=Q(1)
    for k in range(len(nodes)-1,-1,-1):
        index=leaves+k
        if not weights[index]:continue
        c=weights.pop(index);old,piv,b,a,g=nodes[k]
        weights[old]+=c*Q(b,g);weights[piv]-=c*Q(a,g)
    if not weights[T]:raise ArithmeticError('Vanishing target coefficient')
    coeff=[-weights[i]/weights[T] for i in range(nr)]
    residual=dict(target0)
    for c,r in zip(coeff,rows):residual=plus(residual,r,-c)
    if residual:raise ArithmeticError('Search produced an invalid certificate')
    return coeff,rank

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();start=time.monotonic()
    rows,names,targ,cols=candidates()
    co,rank=eliminate(rows,targ,cols)
    records=[]
    for name,c in zip(names,co):
        if not c:continue
        if name[0]=='cayley':
            records.append({'kind':'cayley','word':list(name[1]),'coefficient':str(c)})
        else:
            u,v,g=name
            records.append({'kind':'double_shuffle','u':list(u),'v':list(v),'coefficient':str(c/Q(g))})
    out={'schema':'proveit.cayley-s4.word-certificate.v1','weight':5,'rows':records,
         'description':'Regenerated exact certificate; rows may depend on elimination choices.'}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'candidate_double_shuffle_rows':len(rows)-1,'columns':len(cols),
                      'pivots_until_target_zero':rank,'certificate_rows':len(records),
                      'elapsed_seconds':round(time.monotonic()-start,3)}))
    print(json.dumps(verify(args.output)));print(json.dumps(verify_other(args.output)))
if __name__=='__main__':main()
