#!/usr/bin/env python3
"""Exact rational affine-hull analysis of the calibrated register CFG.

Coordinates are (1,R0,...,R8). A rational subspace overapproximates the
homogenized reachable points. Zero branches intersect a coordinate hyperplane;
positive branches conservatively forget the inequality except known constants.
The pre-existing certified singleton product facts are optional reductions.
"""
from pathlib import Path
from fractions import Fraction as Q
from collections import deque
import argparse,hashlib,importlib.util,json,time
HERE=Path(__file__).resolve().parent
SRC=HERE.parent/'inputs'
spec=importlib.util.spec_from_file_location('graph_interface',SRC/'graph_interface.py')
G=importlib.util.module_from_spec(spec);spec.loader.exec_module(G)
ordered,graph,start,depth=G.graph(json.loads((SRC/'source.json').read_text()))
N=10

def span(rows):
    basis={}
    for row in rows:
        row=list(row)
        for p,v in sorted(basis.items()):
            if row[p]:
                k=row[p];row=[a-k*b for a,b in zip(row,v)]
        p=next((i for i,x in enumerate(row) if x),None)
        if p is None:continue
        k=row[p];row=tuple(x/k for x in row)
        for p0,v in list(basis.items()):
            if v[p]:
                k=v[p];basis[p0]=tuple(a-k*b for a,b in zip(v,row))
        basis[p]=row
    return tuple(basis[p] for p in sorted(basis))

def live(B):return B is not None and any(v[0] for v in B)
def intersect(B,coordinate,constant=0):
    coeff=[v[coordinate]-constant*v[0] for v in B]
    pivot=next((i for i,c in enumerate(coeff) if c),None)
    if pivot is None:return B
    p=B[pivot];den=coeff[pivot]
    rows=[tuple(a-(c/den)*b for a,b in zip(v,p)) for i,(v,c) in enumerate(zip(B,coeff)) if i!=pivot]
    ans=span(rows)
    return ans if live(ans) else None

def fixed(B,coordinate):
    if not live(B):return None
    anchor=next(v for v in B if v[0])
    k=anchor[coordinate]/anchor[0]
    return k if all(v[coordinate]==k*v[0] for v in B) else None

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--reduce-singletons',action='store_true')
ap.add_argument('--output',type=Path,required=True)
args=ap.parse_args()
assert __debug__
product=json.loads((SRC/'source_abstract_facts_k16.json').read_text()) if args.reduce_singletons else None
print('product example',str(product[0])[:250] if product else None,flush=True)

def reduce_at(i,B):
    if not live(B):return None
    if product is not None:
        vals=product[i]
        if vals is None:return None
        for r,mask in enumerate(vals):
            if mask and mask&(mask-1)==0 and mask.bit_length()-1<16:
                B=intersect(B,r+1,mask.bit_length()-1)
                if not live(B):return None
    return B

def move(B,r,d):
    rows=[]
    for v in B:
        a=list(v);a[r+1]+=d*a[0];rows.append(tuple(a))
    return span(rows)

def successors(i,B):
    d=graph[i]
    if d[0]=='INC':yield d[2],move(B,d[1],1)
    elif d[0]=='DEC':
        k=fixed(B,d[1]+1)
        if k is None or k>0:yield d[2],move(B,d[1],-1)
        Z=intersect(B,d[1]+1)
        if live(Z):yield d[3],Z
    elif d[0]=='JUMP':yield d[1],B
    else:assert d==('HALT',)

seed=(1,3,0,0,0,3,0,0,0,0)
facts=[None]*len(graph);facts[start]=(tuple(map(Q,seed)),)
todo=deque([start]);pending={start};updates=0;began=time.monotonic()
while todo:
    i=todo.popleft();pending.remove(i)
    for j,B in successors(i,facts[i]):
        B=reduce_at(j,B)
        if not live(B):continue
        old=facts[j]
        joined=B if old is None else span(old+B)
        if joined!=old:
            facts[j]=joined;updates+=1
            if j not in pending:pending.add(j);todo.append(j)
    if updates and updates%2500==0:print('updates',updates,'queued',len(todo),'seconds',round(time.monotonic()-began,1),flush=True)

def included(A,B):return span(B+A)==B
assert included((tuple(map(Q,seed)),),facts[start])
for i,B in enumerate(facts):
    if live(B):
        for j,C in successors(i,B):
            C=reduce_at(j,C)
            if live(C):assert facts[j] is not None and included(C,facts[j]),(i,j)
forced=[];constant_count=0
for i,B in enumerate(facts):
    if B:
        const=[fixed(B,r+1) for r in range(9)];constant_count+=sum(c is not None for c in const)
        if graph[i][0]=='DEC' and const[graph[i][1]] is not None:
            r=graph[i][1];c=const[r]
            forced.append(dict(index=i,path=ordered[i][0],reg=r,value=str(c),only='zero' if c==0 else 'positive'))
out=dict(status='PASS_RATIONAL_AFFINE_POSTFIXPOINT',source_sha256=hashlib.sha256((SRC/'source.json').read_bytes()).hexdigest(),
         singleton_reduction=args.reduce_singletons,instructions=len(facts),unreachable=[i for i,B in enumerate(facts) if not B],
         forced_decrement_guards=forced,constant_register_facts=constant_count,updates=updates,seconds=time.monotonic()-began,
         dimensions={str(k):sum(B is not None and len(B)==k for B in facts) for k in range(1,11)})
args.output.mkdir(parents=True,exist_ok=True)
(args.output/'summary.json').write_text(json.dumps(out,indent=2)+'\n')
(args.output/'facts.json').write_text(json.dumps([None if B is None else [[str(x) for x in v] for v in B] for B in facts])+'\n')
print(json.dumps(out,indent=2),flush=True)
