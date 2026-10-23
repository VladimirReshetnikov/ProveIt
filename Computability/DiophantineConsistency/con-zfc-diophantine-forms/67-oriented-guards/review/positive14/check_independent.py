#!/usr/bin/env python3
"""Independent exact audit. No imports from the component's builder/checker.
Requires installed SymPy. Universal number theory remains separate.
"""
from pathlib import Path
import json, hashlib, gzip
from collections import Counter
import sympy as S
ROOT=Path(__file__).resolve().parents[2]/'positive'
OUT=Path(__file__).resolve().parent

def check(p,s):
 if not p: raise RuntimeError(s)
def load(p): return json.loads((ROOT/p).read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
C=load('fourteen_positive_degree30.json')
names=C['witnesses']+C['fixed_numerals']; syms=S.symbols(' '.join(names)); lookup=dict(zip(names,syms))
check(len(C['witnesses'])==14 and len(set(names))==18,'inputs')
env={n:S.Poly(x,*syms) for n,x in lookup.items()}
def val(x):return env[x] if isinstance(x,str) else S.Poly(x,*syms)
for n,op,x,y in C['source']:
 check(n not in env and op in ['+','-','*'],'topology/operation')
 a,b=val(x),val(y)
 # Do not expand final squares: all residuals are established before this suffix.
 if all(t in env for t in C['residuals']):break
 env[n]=a+b if op=='+' else a-b if op=='-' else a*b
J,F,alpha,z,f,i,T,w,Y,r,eta,zeta,u,gamma=[lookup[n] for n in C['witnesses']]
beta,K0,MC,MF=[lookup[n] for n in C['fixed_numerals']]
q=beta*J+1; X=w*q; E=X*Y; k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; D=a*a+H; ell=E*k*Y
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J; U=4*q*Y
Z=U*X+H*(U*gamma-k+R+1); Q=D*(f*f-1); V=f*f*(c*T-R)-c
# Independently derived cancellation normal forms, not author certificate imports.
forms=[q**6*(r*r+ell*(2*r-k)-1)+2*q**3*(ell+r)*Y+Y*Y,
2*U*a*c*Z+Z*Z-U*U*(H*c*c+1),
(i*c*c)**2-Q,
Q*V*V-(Q-1)*(V+u)**2-1,
(K0+w)*(q-F-alpha)+q-F-z*(q-1)-1]
info=[]
for n,formula in zip(C['residuals'],forms):
 p=S.Poly(formula,*syms);check(env[n]==p,'literal residual '+n)
 degree=max(sum(m[:14]) for m,v in p.terms()); top=sum(v*S.prod(t**e for t,e in zip(syms,m)) for m,v in p.terms() if sum(m[:14])==degree)
 info.append({'name':n,'degree':degree,'terms':len(p.terms())})
 if n=='main':
  q0=beta*J;E0=w*q0*Y;c0=(eta+zeta)*Y;H0=4*E0;U0=4*q0*Y;R0=q0**3*(q0-F)
  check(S.expand(top-(2*U0*E0*c0*H0*R0+H0**2*R0**2))==0,'degree14 main leading form')
 if n=='aux':check(S.expand(top-2*(w*beta*J*Y)**2*(beta*J)**3*(beta*J-F)*f**4*u)==0,'degree15 auxiliary leading form')
check([r['degree'] for r in info]==[12,14,10,15,2],'degree vector')
# Audit every output suffix gate over independent residual indeterminates.
t=S.symbols('t0:5'); tail=dict(zip(C['residuals'],t)); started=False
for n,op,x,y in C['source']:
 if n in tail:continue
 if (isinstance(x,str) and x not in tail) or (isinstance(y,str) and y not in tail):
  check(not started,'unexpected old-gate suffix input');continue
 started=True
 a=tail[x] if isinstance(x,str) else x;b=tail[y] if isinstance(y,str) else y
 tail[n]=a+b if op=='+' else a-b if op=='-' else a*b
check(S.expand(tail[C['output']]-sum(v*v for v in t))==0,'SOS suffix')
need={C['output']}
for n,op,x,y in reversed(C['source']):
 if n in need:need.update(v for v in [x,y] if isinstance(v,str))
check(set(names)<=need and all(r[0] in need for r in C['source']),'liveness')
check(len(C['source'])==87 and Counter(r[1] for r in C['source'])==Counter({'*':47,'+':24,'-':16}),'gate count')
need=set(C['residuals'])
for n,op,x,y in reversed(C['source']):
 if n in need:need.update(v for v in [x,y] if isinstance(v,str))
systemrows=[r for r in C['source'] if r[0] in need]
check(len(systemrows)==78 and systemrows==load('fourteen_positive_system.json')['source'],'system count')
pins=load('SOURCE_PINS.json')['sources']
for p in pins:check(sha(ROOT/p['local_path'])==p['sha256'],'source hash')
binding=load('coefficients/COEFFICIENT_BINDING.json');ports={}
for row in binding['materialization']['files']:
 blob=(ROOT/'coefficients'/row['file']).read_bytes();raw=gzip.decompress(blob)
 check(hashlib.sha256(blob).hexdigest()==row['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==row['sha256'],'coefficient hash')
 check(len(raw)==row['raw_bytes'],'coefficient length');ports[row['port']]=int.from_bytes(raw,'little')
check(ports['beta']==2**590069-1,'beta binding')
receipt={'status':'PASS','independent_method':'Exact symbolic residual expansion over Z in all 14 variables and four symbolic ports; independent residual-symbol SOS suffix. No component code imports.', 'residuals':info,'polynomial_degree':30,'polynomial_operations':87,'system_operations':78,'source_pins':len(pins),'payloads':len(ports),'reviewed_files':{p:sha(ROOT/p) for p in ['PROOF.md','section.tex','fourteen_positive_degree30.json','fourteen_positive_system.json','SOURCE_PINS.json']},'limits':'Not a kernel proof of inherited Pell rank, compiler, or ZFC calibration. Symbolic coefficients do not make number-theoretic semantics valid for arbitrary tuples.'}
(OUT/'RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
