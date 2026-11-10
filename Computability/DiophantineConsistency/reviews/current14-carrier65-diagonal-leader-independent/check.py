#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];graph=root/'research/carrier65-independent/INCOMING_CARRIER65.json';p=root/'research/current14-carrier65-diagonal-leader';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest();assert sha(graph)=='bf58ed6600eee34d86a802a992e3fd9b999e1835b57a5a83734a40073e1658a7';d=json.loads(graph.read_text());rows={a:(op,x,y) for a,op,x,y in d['source']};assert len(rows)==65 and d['output']=='polynomial'
for a,b in {'ac':('*','a','c'),'a2':('*','a','a'),'Delta':('+','a2','H'),'main_base':('+','X','ac'),'gammaH':('*','gamma','H'),'main_root':('+','main_base','gammaH'),'c2':('*','c','c'),'Dc2':('*','Delta','c2'),'main_square':('*','main_root','main_root'),'N1':('-','main_square','Dc2')}.items():assert rows[a]==b
# Independent exact multivariate sparse integer ring, dimensions are arbitrary.
def one(n,k):return {(0,)*k:n} if n else {}
def var(i,k):
 a=[0]*k;a[i]=1;return {tuple(a):1}
def add(a,b,sgn=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sgn*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for x,u in a.items():
  for y,v in b.items():
   z=tuple(i+j for i,j in zip(x,y));c[z]=c.get(z,0)+u*v
 return {m:v for m,v in c.items() if v}
X,A,C,H,G=(var(i,5) for i in range(5));u=add(X,mul(G,H));ac=mul(A,C);lhs=add(mul(add(u,ac),add(u,ac)),mul(add(mul(A,A),H),mul(C,C)),-1);rhs=add(add(mul(u,u),mul(one(2,5),mul(ac,u))),mul(H,mul(C,C)),-1);assert lhs==rhs
# Exact top coefficient in Z[beta,K,MC,MF]; zero leading sums fail closed.
def plus(a,b,sign=1):
 da,ca=a;db,cb=b
 if da>db:return a
 if db>da:return (db,cb if sign==1 else mul(one(-1,4),cb))
 c=add(ca,cb,sign);assert c,'canceled top requires lower-order terms';return da,c
def times(a,b):
 c=mul(a[1],b[1]);assert c;return a[0]+b[0],c
e={name:(1,one(1,4)) for name in d['witnesses']};e.update({name:(0,var(i,4)) for i,name in enumerate(d['fixed_numerals'])});e.update({k:(0,one(k,4)) for k in (1,3,4)})
for name,op,a,b in d['source']:
 if name=='N1':
  # Verify original apparent degree-22 leading terms cancel before using exact Q identity.
  assert e['main_square']==e['Dc2'];r=plus(e['X'],times(e['gamma'],e['H']));e[name]=plus(plus(times(r,r),times((0,one(2,4)),times(e['ac'],r))),times(e['H'],e['c2']),-1)
 else:e[name]=times(e[a],e[b]) if op=='*' else plus(e[a],e[b],1 if op=='+' else -1)
expected={'N0':(22,-4,14),'N1':(18,16,11),'Na':(62,64,34),'Nt':(2,-2,0),'scaled_Ns':(46,-16,28),'polynomial':(150,-131072,87)}
for name,(deg,coeff,powb) in expected.items():assert e[name]==(deg,{(powb,0,0,0):coeff}),(name,e[name])
# Entire graph, including the canceled Q node, evaluated independently as exact integer t-polynomials.
def conv(a,b):
 r=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):r[i+j]+=x*y
 while len(r)>1 and r[-1]==0:r.pop()
 return r
def comb(a,b,sign):
 r=[(a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
 while len(r)>1 and r[-1]==0:r.pop()
 return r
for beta,K,MC,MF in ((1,0,0,0),(-1,3,-2,7),(2,-5,11,4),(-2,7,5,-3),(3,2,1,9)):
 v={name:[0,1] for name in d['witnesses']};v.update({name:[k] for name,k in zip(d['fixed_numerals'],(beta,K,MC,MF))});v.update({k:[k] for k in (1,3,4)})
 for name,op,a,b in d['source']:v[name]=conv(v[a],v[b]) if op=='*' else comb(v[a],v[b],1 if op=='+' else -1)
 assert len(v['polynomial'])==151 and v['polynomial'][-1]==-131072*beta**87
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/current14-carrier65-dag-draft-independent/check.py')],capture_output=True,check=True,timeout=180)
print(json.dumps({'status':'PASS_EXTERNAL_REVIEW','graph_sha256':sha(graph),'author_checker_sha256':sha(p/'verify.py'),'degree':150,'leading_coefficient':'-131072 * beta^87','integer_polynomial_samples':5,'scope':'external exact arithmetic; beta != 0; not Lean totalDegree or PDF theorem'},indent=2))
