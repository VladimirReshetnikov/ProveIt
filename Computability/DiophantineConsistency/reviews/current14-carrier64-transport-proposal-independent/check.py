#!/usr/bin/env python3
import hashlib,json,gzip,random,subprocess,sys
from pathlib import Path
from collections import Counter
assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
root=Path(__file__).resolve().parents[2];d=root/'research/current14-carrier64-transport-proposal';p=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
assert sha(p)=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e' and sha(d/'graph.json')=='f3bc67492c0aa88c9881bf7e2c39e1586e38b3324305b025b010c0912625af43' and sha(d/'check.py')=='5760992d376c005392fa092e67f5addec212040fa82332d4a0d61efc5253c755'
a=json.loads(p.read_text());b=json.loads((d/'graph.json').read_text());r=json.loads((d/'result.json').read_text());assert len(a['source'])==65 and len(b['source'])==64 and len(b['witnesses'])==14 and b['fixed_numerals']==a['fixed_numerals'];assert b['witnesses']==['C' if x=='alpha' else x for x in a['witnesses']]
orig={n:(o,x,y) for n,o,x,y in a['source']};new={n:(o,x,y) for n,o,x,y in b['source']};assert set(orig)-set(new)=={'C'} and set(new)-set(orig)==set()
assert orig['C']==('-', 'qF','alpha') and orig['gap_product']==('*','qm','qF') and new['gap_product']==('*','q','qF') and orig['gap']==('+','gap_product','alpha') and new['gap']==('-','gap_product','C')
assert all(orig[k]==new[k] for k in new if k not in ('gap','gap_product'));assert [n for n,o,x,y in a['source'] if 'alpha' in (x,y)]==['C','gap'];assert [n for n,o,x,y in a['source'] if 'gap_product' in (x,y)]==['gap']
# Exact sparse ring, independent coordinates, including conditional transport perturbation.
n=8;Z=(0,)*n;one={Z:1}
def V(i):return {tuple(int(j==i) for j in range(n)):1}
def add(x,y,k=1):
 z=x.copy()
 for m,c in y.items():z[m]=z.get(m,0)+k*c
 return {m:c for m,c in z.items() if c}
def sub(x,y):return add(x,y,-1)
def mul(x,y):
 z={}
 for a,ca in x.items():
  for b,cb in y.items():
   m=tuple(u+v for u,v in zip(a,b));z[m]=z.get(m,0)+ca*cb
 return {m:c for m,c in z.items() if c}
q,F,C,z,K,w,delta,h=map(V,range(n));qF=sub(q,F);alpha=sub(qF,C)
assert add(mul(sub(q,one),qF),alpha)==sub(mul(q,qF),C)
def gap(f,c):return sub(mul(q,sub(q,f)),c)
def nt(f,c,zz):return sub(add(mul(add(K,w),c),sub(q,f)),mul(zz,sub(q,one)))
fp=sub(F,delta);cp=add(C,mul(q,delta));zp=add(add(z,mul(delta,add(K,w))),h)
assert gap(fp,cp)==gap(F,C) and sub(nt(fp,cp,zp),nt(F,C,z))==sub(mul(delta,add(add(K,w),one)),mul(h,sub(q,one)))
# Norm-one Pell unit and congruence step with E,Y,xh,kh,j independent.
E,Y,xh,kh,j=map(V,range(5));two=add(one,one);m=mul(E,Y);D=mul(m,add(m,one));rootu=add(mul(two,m),one);x=add(one,mul(E,xh));k=add(mul(two,j),mul(E,kh));xp=add(mul(rootu,x),mul(mul(two,D),k));kp=add(mul(two,x),mul(rootu,k))
assert sub(mul(xp,xp),mul(D,mul(kp,kp)))==sub(mul(x,x),mul(D,mul(k,k))) and all(t[0]>0 for t in sub(xp,one)) and all(t[0]>0 for t in sub(kp,mul(two,add(j,one))))
ports={}
for name,meta in a['coefficient_binding']['ports'].items():
 bts=(p.parent/'coefficients'/meta['file']).read_bytes();assert hashlib.sha256(bts).hexdigest()==meta['gzip_sha256'];raw=gzip.decompress(bts);assert hashlib.sha256(raw).hexdigest()==meta['raw_sha256'] and len(raw)==meta['raw_bytes'];ports[name]=int.from_bytes(raw,'big')
beta,K,MC,MF=(ports[x] for x in ('beta','K0','MC','MF'));q=beta+1;assert beta>=31 and K>0 and 0<MC<beta<MF<2*beta and beta%2==1 and MC%2==0 and q%2==0
for choice in (1,2):
 C=q if choice==1 else q+1;w=1+(q-2)*K if choice==1 else q//2+(q-2)*K;z=2+q*K if choice==1 else 1+(q+2)//2+K*(q+1);G=q*(q-1)-C;R=G*(q*q-1)+MC+q*MF;nt=(K+w)*C+q-1-z*(q-1);E=w*q**4;assert w>0 and z>0 and nt==1 and q-1-C==-choice and 1<R<q**4-q**3<E
 if choice==1:
  assert R%2==0 and E%2==0 and divmod(G,q-1)==(q-2,q-2);tau=E+2-R;ell=E*2*q**3;assert tau>4 and tau*tau-ell*(ell+2)<0
 else:
  assert R%2==1 and (R+1)%2==0 and (2*((R+1)//2)-R-1)%E==0
  base=q-1;u,rem=divmod(G,base);assert (u,rem)==(base-1,base-2) and q-u==2 and u-rem==1 and (K+w)%base==q//2 and (K+w)%base!=2
# Count all reachable operations/inputs and exact live set.
deps={name:(x,y) for name,op,x,y in b['source']};seen=set();todo=[b['output']]
while todo:
 x=todo.pop()
 if x not in seen:
  seen.add(x)
  if x in deps:todo.extend(deps[x])
assert all(x in seen for x in b['witnesses']+b['fixed_numerals']+list(deps)) and Counter(op for _,op,_,_ in b['source'])=={'*':37,'+':15,'-':12}
# The affected inputs occur outside the local expressions only in those same preserved factors.
for name in ('F','C','z'):
 uses={n for n,o,x,y in b['source'] if name in (x,y)}
 assert uses=={'F':{'qF'},'C':{'gap','transport'},'z':{'zqm'}}[name]
out=subprocess.run([sys.executable,'-I','-S','-B',str(d/'check.py')],capture_output=True,text=True,check=True,timeout=180);assert not out.stderr and json.loads(out.stdout)==r
print(json.dumps({'status':'PASS_INDEPENDENT_EXTERNAL_AUDIT','scope':'64-gate exact coordinate rewrite and qualified partial/conditional obstructions; reverse positive-zero equivalence remains open; no Lean/PDF theorem'},indent=2))
