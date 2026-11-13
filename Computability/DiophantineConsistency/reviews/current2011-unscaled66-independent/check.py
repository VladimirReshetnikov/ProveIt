#!/usr/bin/env python3
"""Independent graph factor and specialized exact-degree witness, no Lean."""
import collections,gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2];B=D/'research/current2011-unscaled66';P=D/'candidates/one-page-padding-staircase-carrier65-2011';prime=1000000007
def H(b):return hashlib.sha256(b).hexdigest()
def need(v,s):
 if not v:raise RuntimeError(s)
raw=(B/'polynomial.json').read_bytes(); parentraw=(P/'polynomial.json').read_bytes(); need(H(raw)=='bf9e05905fe84f74edade75ba7d373bd6955aa035867af89a6026d9a21719e75' and H(parentraw)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e','pinned graphs');g=json.loads(raw);p=json.loads(parentraw);a=g['source'];b=p['source'];need(len(a)==66 and len(b)==65 and a[:51]==b[:51],'shared prefix');need(g['witnesses']==p['witnesses'] and g['fixed_numerals']==p['fixed_numerals'] and g['coefficient_binding']==p['coefficient_binding'],'same input metadata')
# Validate all named arithmetic tails against the factored symbolic proof below.
need(a[51:]==[['i2','*','i','i'],['i2Dc2','*','i2','Dc2'],['strongTerm','*','i2Dc2','c2'],['Z','-','f2','strongTerm'],['auxCoefficient','*','Delta','strongTerm'],['V2','*','V','V'],['y2','*','y','y'],['squareGap','-','V2','y2'],['auxProduct','*','auxCoefficient','squareGap'],['Na','+','auxProduct','y2'],['product0','*','N0','N1'],['product1','*','product0','Na'],['product2','*','product1','Nt'],['product3','*','product2','Z'],['polynomial','-','product3',1]],'candidate tail')
need(b[51:]==[['normalized_S','*','i','Dc2'],['normalized_S2','*','normalized_S','normalized_S'],['V2','*','V','V'],['y2','*','y','y'],['V2minusY2','-','V2','y2'],['aux_product','*','normalized_S2','V2minusY2'],['Na','+','aux_product','y2'],['scaled_f2','*','Delta','f2'],['scaled_Ns','-','scaled_f2','normalized_S2'],['product0','*','N0','N1'],['product1','*','product0','Na'],['product3','*','product1','Nt'],['product4','*','product3','scaled_Ns'],['polynomial','-','product4','Delta']],'parent tail')
by={r[0]:r for r in a};need(by['Dc2']==['Dc2','*','Delta','c2'] and by['c2']==['c2','*','c','c'],'shared strong dependencies')
need(by['a']==['a','+','E','Y'] and by['four_a']==['four_a','*',4,'a'] and by['H']==['H','+','four_a',3] and by['a2']==['a2','*','a','a'] and by['Delta']==['Delta','+','a2','H'],'Delta structure')
# Integral multivariate ring on 9 abstract cuts, exact coefficient dictionaries.
N=9;zero=(0,)*N
def var(i):t=[0]*N;t[i]=1;return {tuple(t):1}
def add(x,y,sgn=1):
 z=x.copy()
 for k,v in y.items():z[k]=z.get(k,0)+sgn*v
 return {k:v for k,v in z.items() if v}
def mul(x,y):
 z={}
 for k,v in x.items():
  for j,w in y.items():
   t=tuple(a+b for a,b in zip(k,j));z[t]=z.get(t,0)+v*w
 return {k:v for k,v in z.items() if v}
n0,n1,nt,d,f,i,c2,v2,y2=map(var,range(9)); one={zero:1};st=mul(mul(mul(i,i),d),mul(c2,c2));s2=mul(mul(i,mul(d,c2)),mul(i,mul(d,c2)));need(s2==mul(d,st),'strong identity');na=add(mul(s2,add(v2,y2,-1)),y2);prefix=mul(mul(mul(n0,n1),na),nt);old=add(mul(prefix,add(mul(d,f),s2,-1)),d,-1);new=add(mul(prefix,add(f,st,-1)),one,-1);need(old==mul(d,new),'full factor identity');need(old!=mul(d,add(mul(prefix,add(f,st,-1)),{zero:2},-1)),'false constant control')
# Validate topological order and count reachable operations/inputs.
inputs=set(g['witnesses']+g['fixed_numerals']);known=set(inputs);count=collections.Counter();edges={}
for n,o,x,y in a:
 need(n not in known and o in '+-*' and all(isinstance(t,int) or t in known for t in (x,y)),'topological gate');known.add(n);count[o]+=1;edges[n]=(x,y)
seen=set();leaves=set();stack=[g['output']]
while stack:
 n=stack.pop()
 if n in edges:
  if n not in seen:seen.add(n);stack.extend(edges[n])
 elif isinstance(n,str):leaves.add(n)
need(len(seen)==66 and leaves==inputs and dict(count)=={'*':38,'+':16,'-':12},'live inputs and gates')
# Explicit algebraic cancellation tightens N1 from naive degree 22 to 18.
need(by['main_base']==['main_base','+','X','ac'] and by['main_root']==['main_root','+','main_base','gammaH'] and by['main_square']==['main_square','*','main_root','main_root'] and by['N1']==['N1','-','main_square','Dc2'] and by['ac']==['ac','*','a','c'] and by['gammaH']==['gammaH','*','gamma','H'],'main norm shape')
# N1 = X^2 + 2Xac + 2 gamma H(X+ac) + gamma^2 H^2 - H c^2.
deg={n:1 for n in g['witnesses']};deg.update({n:0 for n in g['fixed_numerals']}); vals={n:[0,1] for n in g['witnesses']};portvals={}
for name,meta in p['coefficient_binding']['ports'].items():
 z=(P/'coefficients'/meta['file']).read_bytes();need(H(z)==meta['gzip_sha256'],'gzip '+name);raw=gzip.decompress(z);need(H(raw)==meta['raw_sha256'] and len(raw)==meta['raw_bytes'],'raw '+name); portvals[name]=int.from_bytes(raw,'big');vals[name]=[portvals[name]%prime]
need(portvals['beta']>0,'positive beta')
def poly(x,y,op):
 z=[0]*(len(x)+len(y)-1 if op=='*' else max(len(x),len(y)))
 if op=='*':
  for i,v in enumerate(x):
   for j,w in enumerate(y):z[i+j]=(z[i+j]+v*w)%prime
 else:
  for i,v in enumerate(x):z[i]=(z[i]+v)%prime
  for i,v in enumerate(y):z[i]=(z[i]+(1 if op=='+' else -1)*v)%prime
 while len(z)>1 and z[-1]==0:z.pop()
 return z
for n,o,x,y in a:
 dx=deg[x] if isinstance(x,str) else 0;dy=deg[y] if isinstance(y,str) else 0; deg[n]=dx+dy if o=='*' else max(dx,dy)
 if n=='N1':
  need((deg['X'],deg['a'],deg['c'],deg['H'],deg['gamma'])==(2,6,5,6,1),'bound inputs');deg[n]=max(2*deg['X'],deg['X']+deg['a']+deg['c'],deg['gamma']+deg['H']+max(deg['X'],deg['a']+deg['c']),2*deg['gamma']+2*deg['H'],deg['H']+2*deg['c']);need(deg[n]==18,'tight N1')
 vals[n]=poly(vals[x] if isinstance(x,str) else [x%prime],vals[y] if isinstance(y,str) else [y%prime],o)
need(deg[g['output']]==138,'degree upper');ray=vals[g['output']];need(len(ray)==139 and ray[-1]==47829043,'nonzero degree-138 ray coefficient')
print(json.dumps({'status':'PASS_INDEPENDENT_EXACT_GRAPH_AUDIT','factor_identity':'parent65 = Delta * candidate66 in Z[variables, ports]','operations':dict(count),'live_gates':len(seen),'live_inputs':len(leaves),'degree_upper':deg[g['output']],'ray':'all 14 variables = t, fixed port bytes modulo 1000000007','ray_degree':len(ray)-1,'ray_leading_coefficient_mod_prime':ray[-1],'beta_mod_prime':portvals['beta']%prime,'zero_equivalence_scope':'Delta positive for strictly positive witnesses and positive beta','scope':'External exact polynomial checks; no Lean or iPRA derivation; fixed port bytes as recorded.'},indent=2,sort_keys=True))
