#!/usr/bin/env python3
"""Derive a positive-coordinate circuit from the audited natural-coordinate AST."""
import collections, copy, hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent
source=P.parent/'nine-sharing-sign14-86gate-candidate/seed.json'
raw=source.read_bytes(); digest=hashlib.sha256(raw).hexdigest()
if digest!='c397c797e39f54bbe4e2a621a15cd94a898a6b44604379aae28a21f0d5861497':raise RuntimeError('source pin')
old=json.loads(raw);N=lambda n:['num',n];V=lambda n:['var',n];A=lambda a,b:['add',a,b];S=lambda a,b:['sub',a,b];M=lambda a,b:['mul',a,b]
b=M(['port','beta'],A(V(1),N(1)));hits=collections.Counter()
def convert(x):
    if x[0]=='add' and x[1][0]=='var' and x[2]==N(1):
        hits['positive_shift']+=1;return copy.deepcopy(x[1])
    if x==S(b,V(2)):
        hits['q_minus_f']+=1;return S(A(M(['port','beta'],V(1)),N(1)),V(2))
    if x[0]=='sub' and x[1][0]=='sub' and x[1][2]==V(2) and x[2]==N(1):
        hits['minus_f']+=1;return S(convert(x[1][1]),V(2))
    if x[0]=='var':return S(copy.deepcopy(x),N(1))
    if x[0] in ('add','sub','mul'):return [x[0],convert(x[1]),convert(x[2])]
    if x[0] in ('num','port'):return copy.deepcopy(x)
    raise ValueError(x[0])
rows=[{'gate':row['gate'],'expr':convert(row['expr'])} for row in old['residuals']]
if hits!={'positive_shift':527,'q_minus_f':9,'minus_f':1}:raise RuntimeError(('rewrite hits',hits))
def ev(e,v,p):
    o=e[0]
    if o=='num':return e[1]
    if o=='var':return v[e[1]]
    if o=='port':return p[e[1]]
    a,c=ev(e[1],v,p),ev(e[2],v,p)
    return a+c if o=='add' else a-c if o=='sub' else a*c if o=='mul' else (_ for _ in ()).throw(ValueError(o))
for off in range(6):
    u={i:1+(i+off)%4 for i in range(1,15)};v={i:x-1 for i,x in u.items()};ports={p:(i+off)%5 for i,p in enumerate(('beta','K0','MC','MF'))}
    for a,c in zip(old['residuals'],rows):
        if ev(a['expr'],v,ports)!=ev(c['expr'],u,ports):raise RuntimeError('assignment control')
nodes=[]; ids={}
def node(op,a,b):
    key=(op,a,b)
    if key not in ids:ids[key]=len(nodes);nodes.append(key)
    return ('node',ids[key])
def lower(e):
    if e[0] in ('add','sub','mul'):return node(e[0],lower(e[1]),lower(e[2]))
    if e[0] in ('var','port','num'):return tuple(e)
    raise ValueError(e[0])
roots=[lower(row['expr']) for row in rows];residual_count=len(nodes);squares=[node('mul',x,x) for x in roots];out=squares[0]
for x in squares[1:]:out=node('add',out,x)
counts=collections.Counter(x[0] for x in nodes);live=set()
def visit(x):
    if x[0]=='node' and x[1] not in live:
        live.add(x[1]);[visit(z) for z in nodes[x[1]][1:]]
visit(out)
if residual_count!=65 or len(nodes)!=74 or len(live)!=74 or counts!={'add':18,'sub':18,'mul':38}:raise RuntimeError(('gate count',residual_count,len(nodes),counts,len(live)))
result={'schema':'sign14-positive-coordinate-residuals-v1','source_sha256':digest,'domain':'14 strictly positive integer variables u[1..14]; natural predecessor v[i]=u[i]-1','ports':'arbitrary integer ports beta, K0, MC, MF','output':'sum of squares of five listed residuals','residuals':rows,'status':'external substitution candidate; Lean coordinate bridge and external file binding unproved'}
encoded=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode();(P/'seed.json').write_bytes(encoded)
print(json.dumps({'status':'PASS_EXTERNAL_POSITIVE_SUBSTITUTION_AND_CIRCUIT','source_sha256':digest,'candidate_sha256':hashlib.sha256(encoded).hexdigest(),'rewrite_hits':dict(hits),'assignment_controls':6,'residual_gates':residual_count,'total_gates':len(nodes),'live_gates':len(live),'gate_counts':dict(counts),'scope':'Exact ordered-subtree-sharing arithmetic DAG, positive input domain, no minimality or Lean/file-binding claim'},sort_keys=True))
