#!/usr/bin/env python3
"""Independent conditional repair controls and exact Pell algebra; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-folded-root86-negated-positive-bt';Q=D/'reviews/ordinary13-folded-root86-negated-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','c7eb54d7750c1b8db428d48408e61e1868c5feaf0584b6e31054f5acf4df0bff'),(P/'check.py','a5d92b4e7d141b43bf0ed624f2a9a733137473a04686c44c1f8d89263e950388'),(P/'result.json','88b3bbe0ed9245592e40a4055849513d274455b17635a2cb180e8f9362fdc435'),(Q/'check.py','cddcc499719950c817bafe2fe24629fc0ddbfac11f6a3e51ae111099f16dd6ab'),(Q/'result.json','574e8da4b43dc44da72193676892ddb5971db2929e67d4f036af43ed9b99199e')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-negated-positive-bt-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='efda325dc716c4512f2ba2a9c38bc5f6936060c05c51178f4cbd1d8262ce4824'
for p in (P,Q):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
for path in ('research/ordinary13-four-square88-30/candidate.json','research/ordinary13-folded-root86-negated/candidate.json'):
 g=json.loads((D/path).read_text());deps={n:{n} for n in g['witnesses']+g['fixed_numerals']}
 for n,op,a,b in g['source']:deps[n]=set().union(*(deps[x] for x in (a,b) if isinstance(x,str)))
 assert 'r' in deps['A0'] and all('r' not in deps[n] for n in ('A1','Fa','g72','Bt','k'))
# Symbolically verify descent preserves the Pell norm, its inverse, and the
# strict-positive descent comparisons in a free integer polynomial ring.
def add(a,b,sgn=1):
 z=a.copy()
 for k,v in b.items():z[k]=z.get(k,0)+sgn*v
 return {k:v for k,v in z.items() if v}
def mul(a,b):
 z={}
 for k,v in a.items():
  for l,w in b.items():
   t=tuple(sorted(k+l));z[t]=z.get(t,0)+v*w
 return {k:v for k,v in z.items() if v}
def scalar(n,a):return {k:n*v for k,v in a.items() if n*v}
def v(n):return {(n,):1}
one={():1};m,k,tau=map(v,('m','k','tau'));A=add(scalar(2,m),one);N=mul(m,add(m,one));kp=add(mul(A,k),scalar(2,tau),-1);tp=add(mul(A,tau),scalar(2,mul(N,k)),-1)
norm=add(mul(tau,tau),mul(N,mul(k,k)),-1);newnorm=add(mul(tp,tp),mul(N,mul(kp,kp)),-1);assert newnorm==norm
assert add(mul(A,kp),scalar(2,tp))==k and add(mul(A,tp),scalar(2,mul(N,kp)))==tau
assert add(mul(mul(A,k),mul(A,k)),scalar(4,mul(tau,tau)),-1)==add(mul(k,k),scalar(4,norm),-1)
# Main radicand's gap to successive squares is c*(2*A-c) and c²-1.
A,c=map(v,('A','c'));d2=add(one,mul(add(mul(A,A),one,-1),mul(c,c)));sq=mul(mul(A,c),mul(A,c));lower=mul(add(mul(A,c),one,-1),add(mul(A,c),one,-1))
assert add(sq,d2,-1)==add(mul(c,c),one,-1) and add(d2,lower,-1)==mul(c,add(scalar(2,A),c,-1))
print(json.dumps({'status':'PASS_CONDITIONAL_REPAIR','dependent_residuals':'A0 only','pell_descent_norm_and_inverse':True,'main_square_gap_identities':True,'scope':'positive candidate zero with beta>0 and Bt>0; no Bt positivity or unrestricted reverse claim; no Lean'},indent=2))
