#!/usr/bin/env python3
"""Signed-fold forward map and scalar shift checks; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary13-folded-root86-negated-forward';Q=D/'reviews/ordinary13-folded-root86-negated-independent'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,h in [(P/'README.md','c4bd9700bcbedbff97f6777a7ac714cc50a3b1febe021498afa2fb87600be6ef'),(P/'check.py','dbf1b900d8d2b17459db65ab9f9f4e4d47e0587b6ed222dd3e46ed54dbf052a1'),(P/'result.json','68c167b3afdda154ba3986641eb0e4235f8afcec96f35fadcd7d909a24503854'),(Q/'check.py','cddcc499719950c817bafe2fe24629fc0ddbfac11f6a3e51ae111099f16dd6ab'),(Q/'result.json','574e8da4b43dc44da72193676892ddb5971db2929e67d4f036af43ed9b99199e')]:assert sha(p)==h,p
readme=(P/'README.md').read_bytes();tail=b'\nIndependent external review is recorded in\n`../../reviews/ordinary13-folded-root86-negated-forward-independent/`.\n';assert readme.endswith(tail) and hashlib.sha256(readme[:-len(tail)]).hexdigest()=='ed941d1dd6c458590267dbff0cb9a504e6f1d166bcee7e0019f964266840b6c6'
for p in (P,Q):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=180);assert not r.stderr and r.stdout==(p/'result.json').read_bytes()
for path in ('research/ordinary13-four-square88-30/candidate.json','research/ordinary13-folded-root86-negated/candidate.json'):
 g=json.loads((D/path).read_text());deps={n:{n} for n in g['witnesses']+g['fixed_numerals']}
 for n,op,a,b in g['source']:
  deps[n]={n} if n=='G' else set().union(*(deps[x] for x in (a,b) if isinstance(x,str)))
 assert all(not ({'F','alpha','r'} & deps[n]) for n in ('R','A1','Fa','g72'))
# Exact symbolic shift: q=b+1; F'=F+b and alpha'=alpha+b².
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
def v(n):return {(n,):1}
one={():1};b,F,alpha,X,K=map(v,('b','F','alpha','X','K'));q=add(one,b);Fnew=add(F,b);alphanew=add(alpha,mul(b,b));C=add(add(q,F,-1),alpha,-1);Cn=add(add(q,Fnew,-1),alphanew,-1);G=add(mul(b,add(q,F,-1)),alpha);Gn=add(mul(b,add(q,Fnew,-1)),alphanew)
assert Gn==G and Cn==add(C,mul(q,b),-1)
B=add(mul(C,add(X,mul(K,q))),mul(F,q),-1);Bn=add(mul(Cn,add(X,mul(K,q))),mul(Fnew,q),-1)
assert Bn==add(B,mul(mul(q,b),add(add(X,mul(K,q)),one)),-1)
# Positive root is chosen so the shifted carrier's quotient is +tau.
ell,k,s,t,tau=map(v,('ell','k','s','t','tau'));sigma=add(add(add(add(ell,k),s),t,-1),tau,-1)
assert add(add(add(add(ell,k),sigma,-1),s),t,-1)==tau
print(json.dumps({'status':'PASS_SCOPED_FORWARD_MAP','scalar_shift_identities':True,'residual_dependency_cut':'G','first_root_identity':True,'scope':'parent positive zero to signed-fold positive zero for beta>0 K0>=0; negative-Bt fixed-coordinate obstruction; no reverse or Lean claim'},indent=2))
