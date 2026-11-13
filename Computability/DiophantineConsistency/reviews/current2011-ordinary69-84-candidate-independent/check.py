#!/usr/bin/env python3
"""Independent check of the 69-row rewrite and its fixed-byte degree."""
import collections, gzip, hashlib, json, subprocess, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
P=D/'research/current2011-ordinary69-84-candidate'; Q=D/'research/current2011-ordinary70-84-candidate'
def sha(b): return hashlib.sha256(b).hexdigest()
def need(v,s):
    if not v: raise RuntimeError(s)
gb=(P/'polynomial.json').read_bytes(); pb=(Q/'polynomial.json').read_bytes()
need(sha(gb)=='c9781e95b9d8e3124afadfe3ee5874eb3eb76ce9f1aaef02c7b3bf49ed93e80a','candidate graph pin')
need(sha(pb)=='bb7df3586252e9c85be225a0373a8586c2c2f841683cc5f4b6f57f02175447e5','parent pin')
g=json.loads(gb); p=json.loads(pb)
need(g['witness_domain']==p['witness_domain']=='strictly positive integers' and g['witnesses']==p['witnesses'] and g['fixed_numerals']==p['fixed_numerals'],'interface')
need(g['parent_graph_sha256']==sha(pb) and g['source'][:61]==p['source'][:61] and g['coefficient_binding']==p['coefficient_binding'],'prefix and metadata')
expected_new=[['Na2','*','Na','Na'],['PQ','*','N0','N1'],['PQW','*','PQ','Nt'],['PQWminus2','-','PQW',2],['PQWproduct','*','PQW','PQWminus2'],['strong2','*','strong_residual','strong_residual'],['sum1','+','Na2','strong2'],['polynomial','+','sum1','PQWproduct']]
expected_old=[['Na2','*','Na','Na'],['PQ','*','N0','N1'],['PQW','*','PQ','Nt'],['rPQW','-','PQW',1],['rPQW2','*','rPQW','rPQW'],['strong2','*','strong_residual','strong_residual'],['sum1','+','Na2','rPQW2'],['sum2','+','sum1','strong2'],['polynomial','-','sum2',1]]
need(g['source'][61:]==expected_new and p['source'][61:]==expected_old and g['output']==p['output']=='polynomial','complete tails')
# Exact sparse-polynomial evaluation of both complete tails, over five free prefix values.
one=(0,)*5
def add(x,y,k=1):
 z=x.copy()
 for m,c in y.items(): z[m]=z.get(m,0)+k*c
 return {m:c for m,c in z.items() if c}
def mul(x,y):
 z={}
 for m,c in x.items():
  for n,d in y.items():
   e=tuple(a+b for a,b in zip(m,n)); z[e]=z.get(e,0)+c*d
 return {m:c for m,c in z.items() if c}
cuts=['N0','N1','Nt','Na','strong_residual']
def tail(rows):
 v={x:{tuple(int(i==j) for i in range(5)):1} for j,x in enumerate(cuts)}
 def get(x): return {one:x} if type(x)==int and x else ({} if x==0 else v[x])
 for n,o,a,b in rows:
  x,y=get(a),get(b); v[n]=mul(x,y) if o=='*' else add(x,y,1 if o=='+' else -1)
 return v['polynomial']
need(tail(expected_new)==tail(expected_old),'ring identity')
known=set(g['witnesses']+g['fixed_numerals']); need(len(known)==18,'distinct inputs'); edges={}; count=collections.Counter()
for n,o,a,b in g['source']:
 need(n not in known and o in ('+','-','*') and all(type(x)==int or x in known for x in (a,b)),'topology'); known.add(n);edges[n]=(a,b);count[o]+=1
seen=set();leaves=set();todo=[g['output']]
while todo:
 n=todo.pop()
 if n in edges:
  if n not in seen: seen.add(n);todo.extend(edges[n])
 elif type(n)==str: leaves.add(n)
need(g['operations']==len(g['source'])==len(seen)==69 and count=={'*':38,'+':18,'-':13} and leaves==set(g['witnesses']+g['fixed_numerals']),'liveness and gates')
# Verify the actual relative metadata path, rather than reconstructing a convenient path.
need(g['coefficient_binding']['path']=='../fourteen-nonzero-spheres/coefficients/','metadata relative path')
prime=1000000007;vals={};total=0
for name,meta in g['coefficient_binding']['ports'].items():
 path=(P/g['coefficient_binding']['path']/meta['file']).resolve(); gz=path.read_bytes(); raw=gzip.decompress(gz)
 need(sha(gz)==meta['gzip_sha256'] and sha(raw)==meta['raw_sha256'] and len(raw)==meta['raw_bytes'] and int.from_bytes(raw,'big').bit_length()==meta['bits'],'payload '+name)
 vals[name]=int.from_bytes(raw,'big')%prime;total+=len(raw)
need(set(vals)==set(g['fixed_numerals']) and total==g['coefficient_binding']['raw_bytes']==47313,'payload interface')
# The only refined bound is justified by cancellation of (a*c)^2 in N1.
r={x[0]:x for x in g['source']}
shape={'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']}
need(all(r[k]==v for k,v in shape.items()),'N1 exact cancellation shape')
deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in vals}); pol={n:[0,1] for n in g['witnesses']};pol.update({n:[v] for n,v in vals.items()})
def poly(x,y,o):
 z=[0]*(len(x)+len(y)-1 if o=='*' else max(len(x),len(y)))
 if o=='*':
  for i,a in enumerate(x):
   for j,b in enumerate(y): z[i+j]=(z[i+j]+a*b)%prime
 else:
  for i,a in enumerate(x): z[i]=(z[i]+a)%prime
  for i,b in enumerate(y): z[i]=(z[i]+(b if o=='+' else -b))%prime
 while len(z)>1 and z[-1]==0:z.pop()
 return z
for n,o,a,b in g['source']:
 da=deg[a] if type(a)==str else 0; db=deg[b] if type(b)==str else 0;deg[n]=da+db if o=='*' else max(da,db)
 if n=='N1':
  need(tuple(deg[k] for k in ('X','a','c','H','gamma'))==(2,6,5,6,1),'bound inputs')
  deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c'])
 pol[n]=poly(pol[a] if type(a)==str else [a%prime],pol[b] if type(b)==str else [b%prime],o)
need(deg['polynomial']==len(pol['polynomial'])-1==84 and pol['polynomial'][-1]==589155221,'degree')
check=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],capture_output=True)
need(check.returncode==0 and check.stdout==(P/'result.json').read_bytes(),'author rerun')
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','candidate_sha256':sha(gb),'parent_sha256':sha(pb),'gates':dict(count),'live_rows':len(seen),'live_inputs':len(leaves),'port_bytes':total,'degree_upper':deg['polynomial'],'ray_degree':len(pol['polynomial'])-1,'ray_prime':prime,'ray_leading_coefficient':pol['polynomial'][-1],'scope':'External graph equality and fixed-byte degree, not a Lean syntax binding or iPRA theorem.'},sort_keys=True,indent=2))
