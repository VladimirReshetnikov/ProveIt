#!/usr/bin/env python3
"""Independent exact universal norm check from the emitted DAG, no producer imports."""
from pathlib import Path
from collections import defaultdict,Counter
from itertools import product
import hashlib,json
R=Path(__file__).resolve().parents[1]/'roots';F=R/'integer12_degree512.json';g=json.loads(F.read_text());nodes=g['nodes'];reg=g['named_registers']
def add(a,b,sign=1):
 c=defaultdict(int,a)
 for m,v in b.items():c[m]+=sign*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c=defaultdict(int)
 for m,v in a.items():
  for n,w in b.items():c[tuple(x+y for x,y in zip(m,n))]+=v*w
 return {m:v for m,v in c.items() if v}
one={(0,)*5:1}
def var(i):return {tuple(1 if j==i else 0 for j in range(5)):1}
# Variables Z,A,B,C,D. s=Z², aa=A²,bb=B²,cc=C²,dd=D².
bound={reg[k]:mul(var(i),var(i)) for i,k in enumerate(('s','aa','bb','cc','dd'))}
cache={}
def ev(i):
 if i in bound:return bound[i]
 if i in cache:return cache[i]
 n=nodes[i];op=n[0]
 if op=='integer':v={(0,)*5:n[1]} if n[1] else {}
 elif op in ['add','sub','mul']:
  a,b=ev(n[1]),ev(n[2]);v=mul(a,b) if op=='mul' else add(a,b,1 if op=='add' else -1)
 else:raise ValueError('Unexpected leaf beyond norm cut: '+str(n))
 cache[i]=v;return v
norm=one
for signs in product([-1,1],repeat=4):
 factor=var(0)
 for i,s in enumerate(signs,1):factor=add(factor,var(i),-s)
 norm=mul(norm,factor)
actual=ev(g['output'])
if actual!=norm:raise ValueError('Emitted norm differs from16-factor product')
# Verify exact homogeneity and pure dd^8 coefficient, and upper degrees of actual circuit.
if any(sum(m)!=16 for m in actual):raise ValueError('Nonhomogeneous norm')
if actual.get((0,0,0,0,16))!=1:raise ValueError('Missing monic auxiliary16th power')
deg=[]
for n in nodes:
 if n[0]=='variable':d=1
 elif n[0] in ['integer','coefficient']:d=0
 elif n[0]=='mul':d=deg[n[1]]+deg[n[2]]
 else:d=max(deg[n[1]],deg[n[2]])
 deg.append(d)
cutdegs={k:deg[reg[k]] for k in ('s','aa','bb','cc','dd','U','Q','V','Cy','Delta','I','Fs','R','F')}
if cutdegs['dd']!=64 or any(cutdegs[k]>=64 for k in ('s','aa','bb','cc')):raise ValueError('Unique maximal input not verified')
live=set()
def visit(i):
 if i in live:return
 live.add(i)
 if nodes[i][0] in ['add','sub','mul']:
  visit(nodes[i][1]);visit(nodes[i][2])
visit(g['output']);counts=Counter(nodes[i][0] for i in live if nodes[i][0] in ['add','sub','mul'])
if len(live)!=len(nodes) or sum(counts.values())!=132:raise ValueError('Topology/count')
receipt={'status':'PASS','equation_sha256':hashlib.sha256(F.read_bytes()).hexdigest(),'independent_exact_16_factor_product':True,'universal_norm_monomials':len(norm),'homogeneous_degree_in_squared_inputs':8,'auxiliary_input_power8_coefficient':1,'cut_degree_upper_bounds':cutdegs,'all_nodes_live':True,'operations':sum(counts.values()),'operation_counts':dict(counts),'boundary':'Full norm identity and topology verified; exact front-leading nonvanishing supplied in separate mathematical review.'}
(Path(__file__).parent/'ROOTS12_NORM_CHECK.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
