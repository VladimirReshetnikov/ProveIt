#!/usr/bin/env python3
"""Emit a finite integer arithmetic circuit for the certified 92-variable polynomial."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent
def canon(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def build(source,cert):
 defs={s['variable']:{tuple(m):c for c,m in s['restoration_source_terms']} for s in cert['steps']}
 free=cert['free_source_variables'];nodes=[];intern={};memo={};gray=set()
 def node(key):
  if key in intern:return intern[key]
  i=len(nodes);nodes.append(list(key));intern[key]=i;return i
 def const(c):return node(('const',c))
 zero=const(0);one=const(1)
 def binary(op,a,b):
  if op=='add':
   if a==zero:return b
   if b==zero:return a
  if op=='mul':
   if a==zero or b==zero:return zero
   if a==one:return b
   if b==one:return a
  if op in ('add','mul') and a>b:a,b=b,a
  return node((op,a,b))
 def polynomial(ts):
  z=zero
  for c,mon in ts:
   term=const(c)
   for v in mon:term=binary('mul',term,variable(v))
   z=binary('add',z,term)
  return z
 freeids={v:i for i,v in enumerate(free)}
 def variable(v):
  if v in memo:return memo[v]
  if v in freeids:memo[v]=node(('input',freeids[v]));return memo[v]
  if v in gray:raise ValueError('cyclic source definition')
  gray.add(v);value=polynomial([[c,list(m)] for m,c in sorted(defs[v].items())]);gray.remove(v);memo[v]=value;return value
 residuals=[polynomial(source['residuals'][i]['terms']) for i in cert['retained_source_rows']]
 total=zero
 for r in residuals:total=binary('add',total,binary('mul',r,r))
 live=set();stack=[total]
 while stack:
  i=stack.pop()
  if i in live:continue
  live.add(i)
  if nodes[i][0] in ('add','mul','sub'):stack.extend(nodes[i][1:])
 keep=sorted(live);ren={v:i for i,v in enumerate(keep)}
 emitted=[]
 for i in keep:
  nd=nodes[i];emitted.append([nd[0],*[ren[j] for j in nd[1:]]] if nd[0] in ('add','mul','sub') else nd)
 return {'schema':'ordinary-integer-arithmetic-circuit-v1','domain':'unrestricted integers','input_count':len(free),'input_source_coordinates':free,'source_sha256':cert['source_sha256'],'nodes':emitted,'residual_outputs':[ren[r] for r in residuals],'output':ren[total],'primitive_operations':['add','mul'],'meaning':'sum of the squares of all residual_outputs'}
def main():
 s=json.loads((ROOT/'sources/source191.json').read_text());c=json.loads((ROOT/'projection92.json').read_text());p=build(s,c);(ROOT/'circuit92.json').write_bytes(canon(p));ops=sum(n[0] in ('add','mul','sub') for n in p['nodes']);lit=max(abs(n[1]) for n in p['nodes'] if n[0]=='const');print(json.dumps({'nodes':len(p['nodes']),'binary_arithmetic_gates':ops,'largest_literal_integer':lit,'inputs':p['input_count']}))
if __name__=='__main__':main()
