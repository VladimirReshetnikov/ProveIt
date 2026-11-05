#!/usr/bin/env python3
"""Independent current-port candidate graph, degree and conditional forward-map checks."""
import collections,gzip,hashlib,json,subprocess,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2]
def H(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
P=D/'research/current2011-ordinary67-94-candidate';G=D/'research/fourteen-nonzero-spheres/polynomial71.json';S=G.parent;prime=1000000007
need(H(P/'polynomial.json')=='d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb' and H(G)=='937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2','graph pins');g=json.loads((P/'polynomial.json').read_text()); parent=json.loads(G.read_text());need(g['source'][:51]==parent['source'][:51] and g['witnesses']==parent['witnesses'] and g['fixed_numerals']==parent['fixed_numerals'] and g['coefficient_binding']==parent['coefficient_binding'],'parent prefix and ports')
need(g['source'][51:]==[['I','*','i','c2'],['I2','*','I','I'],['f2m1','-','f2',1],['Aaux','*','Delta','f2m1'],['V2','*','V','V'],['y2','*','y','y'],['aux_gap','-','V2','y2'],['aux_term','*','Aaux','aux_gap'],['Na','+','aux_term','y2'],['strong_residual','-','I2','Aaux'],['Ns','+','strong_residual',1],['prod0','*','N0','N1'],['prod1','*','prod0','Na'],['prod2','*','prod1','Nt'],['prod3','*','prod2','Ns'],['polynomial','-','prod3',1]],'candidate tail')
known=set(g['witnesses']+g['fixed_numerals']);edges={};counts=collections.Counter()
for n,o,x,y in g['source']:
 need(n not in known and o in '+-*' and all(isinstance(v,int) or v in known for v in (x,y)),'topological graph');known.add(n);edges[n]=(x,y);counts[o]+=1
seen=set();leaves=set();todo=[g['output']]
while todo:
 n=todo.pop()
 if n in edges:
  if n not in seen:seen.add(n);todo.extend(edges[n])
 elif isinstance(n,str):leaves.add(n)
need(len(seen)==67 and leaves==set(g['witnesses']+g['fixed_numerals']) and dict(counts)=={'*':37,'+':17,'-':13},'liveness and operations')
# Check N1 cancellation shape before using its exact degree-18 bound.
r={z[0]:z for z in g['source']};need(all(r[n]==v for n,v in {'a':['a','+','E','Y'],'four_a':['four_a','*',4,'a'],'H':['H','+','four_a',3],'a2':['a2','*','a','a'],'Delta':['Delta','+','a2','H'],'ac':['ac','*','a','c'],'main_base':['main_base','+','X','ac'],'gammaH':['gammaH','*','gamma','H'],'main_root':['main_root','+','main_base','gammaH'],'main_square':['main_square','*','main_root','main_root'],'c2':['c2','*','c','c'],'Dc2':['Dc2','*','Delta','c2'],'N1':['N1','-','main_square','Dc2']}.items()),'N1 shape')
deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']});poly={n:[0,1] for n in g['witnesses']}
for n,m in g['coefficient_binding']['ports'].items():
 z=(S/'coefficients'/m['file']).read_bytes();need(hashlib.sha256(z).hexdigest()==m['gzip_sha256'],'gzip '+n);raw=gzip.decompress(z);need(hashlib.sha256(raw).hexdigest()==m['raw_sha256'] and len(raw)==m['raw_bytes'],'raw '+n);poly[n]=[int.from_bytes(raw,'big')%prime]
def univ(x,y,op):
 z=[0]*(len(x)+len(y)-1 if op=='*' else max(len(x),len(y)))
 if op=='*':
  for i,a in enumerate(x):
   for j,b in enumerate(y):z[i+j]=(z[i+j]+a*b)%prime
 else:
  for i,a in enumerate(x):z[i]=(z[i]+a)%prime
  for i,b in enumerate(y):z[i]=(z[i]+(1 if op=='+' else -1)*b)%prime
 while len(z)>1 and not z[-1]:z.pop()
 return z
for n,o,x,y in g['source']:
 dx=deg[x] if isinstance(x,str) else 0;dy=deg[y] if isinstance(y,str) else 0;deg[n]=dx+dy if o=='*' else max(dx,dy)
 if n=='N1':
  need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'degree inputs');deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c'])
 poly[n]=univ(poly[x] if isinstance(x,str) else [x%prime],poly[y] if isinstance(y,str) else [y%prime],o)
need(deg['polynomial']==94 and len(poly['polynomial'])-1==94 and poly['polynomial'][-1]==495675807,'exact degree 94')
need(not any('i' in row[2:] for row in g['source'][:51]),'forward map changes prefix')
# Universal ring check for i_new=Delta*i_old. Variables d,i,c,f,G.
N=5;zz=(0,)*N;one={zz:1}
def atom(j):
 z=[0]*N;z[j]=1;return {tuple(z):1}
def plus(a,b,sign=1):
 r=a.copy()
 for k,v in b.items():r[k]=r.get(k,0)+sign*v
 return {k:v for k,v in r.items() if v}
def times(a,b):
 r={}
 for k,v in a.items():
  for q,w in b.items():
   z=tuple(x+y for x,y in zip(k,q));r[z]=r.get(z,0)+v*w
 return {k:v for k,v in r.items() if v}
d,i,c,f,G=map(atom,range(5));ic2=times(i,times(c,c));S=plus(times(f,f),times(d,times(ic2,ic2)),-1);I2=times(times(d,d),times(ic2,ic2));A=times(d,plus(times(f,f),one,-1));need(plus(I2,A,-1)==times(d,plus(one,S,-1)),'forward strong identity');need(times(plus(A,I2,-1),G)==times(times(d,plus(S,one,-1)),G),'forward auxiliary identity')
for file,h in [('check.py','d55b77eeb02635efbb6a91e38571c347ab057b7d0876fdd07f33282d88a22770'),('result.json','28fa605de3c317d649e240f9e71da3d576f50d812a4e1212edb52df64ac9cf9d'),('forward_check.py','ef40da2418160ddf166b9ef817311722c667e1a36ba041e7475f6113b8136b18'),('forward-result.json','1be665151dff6a537821624f3dfe7aec9ec42d375c54840813f85165927b1a53')]:need(H(P/file)==h,'author pin '+file)
for script,result in [('check.py','result.json'),('forward_check.py','forward-result.json')]:
 q=subprocess.run([sys.executable,'-I','-S','-B',str(P/script)],capture_output=True);need(q.returncode==0 and q.stdout==(P/result).read_bytes(),'author rerun '+script)
print(json.dumps({'status':'PASS_SCOPED_INDEPENDENT_REVIEW','operations':dict(counts),'live_rows':len(seen),'live_inputs':len(leaves),'degree_upper':94,'degree_lower_ray':94,'ray_modulus':prime,'ray_leading_coefficient':poly['polynomial'][-1],'forward_identities':'exact polynomial identities; strong-norm-one condition required','scope':'Candidate graph, fixed-byte degree, and conditional forward algebra only; no same-zero reverse implication or iPRA theorem.'},indent=2,sort_keys=True))
