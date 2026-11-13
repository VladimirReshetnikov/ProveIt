#!/usr/bin/env python3
"""Independent literal cuts and signed-quotient source review; no Lean."""
from functools import lru_cache
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009')
a=pin('research/ordinary14-natural79-factor-residues-draft/Natural79ResidueShapes.lean','b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38')
u=pin('research/ordinary14-natural79-factor-residues-draft/Natural79ConcreteUnits.lean','253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d')
mag=pin('Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean','c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c')
quot=pin('Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884')
g=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
assert '∃ a : V, (x=ι a ∨ x= -ι a) ∧ x*x=ι (a*a)' in mag
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n) :' in quot
assert '∃ t : V, z=m*t ∧ t*t=n' in quot
for name in ('main_eval_cut','atoms_at_zero_w','main_norm_of_zero_w_zero','scale_pos','signed_quotient_of_zero_w_zero'):assert 'theorem '+name in s
start=s.index('theorem main_norm_of_zero_w_zero');stop=s.index(' := by',start);sig=s[start:stop]
assert '(hbeta : (p 0 : DiffRing V)=ι beta)' in sig and '(hw : v 6=0)' in sig and '(hz : InternalZero' in sig
assert not any(x in sig for x in ('(hb :','(hJ :','(hK','(hgamma'))
start=s.index('theorem signed_quotient_of_zero_w_zero');stop=s.index(' := by',start);sig=s[start:stop]
assert '(hb : 0<beta)' in sig and '(hJ : 0<v 0)' in sig and '(hw : v 6=0)' in sig
assert 'units.2.1' in s and 'rcases hsgn with hp | hn' in s and 'refine ⟨ι t,' in s and 'refine ⟨-ι t,' in s
assert 'theorem main_shape' in a and 'theorem units_of_zero_w_zero' in u
# Exact sparse-polynomial graph cuts, with arbitrary symbolic beta and zero w.
rows={n:(op,x,y) for n,op,x,y in g['source']}
def const(n):return {} if n==0 else {():n}
def var(n):return {(n,):1}
def add(a,b):
 out=dict(a)
 for k,v in b.items():out[k]=out.get(k,0)+v
 return {k:v for k,v in out.items() if v}
def neg(a):return {k:-v for k,v in a.items()}
def mul(a,b):
 out={}
 for x,u in a.items():
  for y,v in b.items():
   k=tuple(sorted(x+y));out[k]=out.get(k,0)+u*v
 return {k:v for k,v in out.items() if v}
@lru_cache(None)
def ev(t):
 if type(t) is int:return const(t)
 if t=='n_w':return const(0)
 if t not in rows:return var(t)
 op,x,y=rows[t];x=ev(x);y=ev(y)
 return add(x,y) if op=='+' else add(x,neg(y)) if op=='-' else mul(x,y)
J,beta,ss,eta,zeta=map(var,('n_J','beta','n_s','n_eta','n_zeta'));one=const(1)
q=add(one,mul(J,beta));y=mul(mul(mul(q,q),q),add(ss,one));k=add(add(eta,one),add(zeta,one));c=add(add(eta,one),mul(y,k));U=mul(y,mul(q,q))
assert ev('a')==y and ev('c')==c and ev('U')==U
assert ev('Delta')==add(mul(y,y),add(mul(const(4),y),const(3)))
# Algebra of both quotient signs: (-t)^2=t^2, -(U*t)=U*(-t).
for U0 in range(1,10):
 for t in range(10):
  for sign in (-1,1):assert sign*(U0*t)==U0*(sign*t) and (sign*t)**2==t*t
for name in ('main_norm_of_zero_w_zero','signed_quotient_of_zero_w_zero'):
 assert '#print axioms DiophantineConsistency.Natural79ZeroWMainNormDraft.'+name in s
print(json.dumps({'scope':'exact graph cuts, source signatures and quotient sign algebra; no Lean/model theorem','pinned_sources':6,'zero_w_atom_cuts':4,'signed_quotient_controls':180,'axiom_reports_unexecuted':2},sort_keys=True,indent=2))
