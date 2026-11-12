#!/usr/bin/env python3
"""Deterministic inert source rewrites and bounded exact graph checks; no Lean."""
from pathlib import Path
from functools import lru_cache
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
paths={
 'main':('research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009'),
 'jpos':('research/ordinary14-natural79-zero-w-jpos-draft/Natural79ZeroWJPos.lean','f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a'),
 'root':('research/ordinary14-natural79-zero-w-root-cut-draft/Natural79ZeroWRootCut.lean','c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec'),
 'div':('research/ordinary14-natural79-dvd-reflection-slim-draft/Natural79ZeroWDivisibility.lean.src','4ab36ba289a4cfce93d80bcc6bcb2cc75f0ca2a64d0a729b076846775dac0896'),
 'end':('research/ordinary14-natural-forced-w79-ipra-draft/Natural79Endpoint.lean','9b527ff7a8b6e166869f2565b83a8c37956680d538c49557de9c82ea1a6041e6'),
 'graph':('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5')}
def sha(x):return hashlib.sha256(x).hexdigest()
s={}
for k,(p,h) in paths.items():
 b=(D/p).read_bytes();assert sha(b)==h,(k,sha(b));s[k]=b.decode()
def once(text,a,b):
 assert text.count(a)==1,repr(a);return text.replace(a,b)
helper=s['jpos'].split('/-- The positive signed unit gives ring value one. -/',1)[1].split('/-- At J=w=0',1)[0]
assert helper.startswith('\ntheorem eval_one_of_pair_unit') and 'linarith' in helper
m=s['main']
m=once(m,'import Natural79ZeroWJPos\n','import Natural79ConcreteUnits\n')
m=once(m,'open Natural79ResidueShapesDraft Natural79ConcreteUnitsDraft Natural79ZeroWJPosDraft','open Natural79ResidueShapesDraft Natural79ConcreteUnitsDraft')
m=once(m,'/-- Main factor\'s evaluation', '/-- The copied pair-unit evaluation lemma; attribution: Natural79ZeroWJPosDraft. -/'+helper+'\n/-- Main factor\'s evaluation')
m=once(m,'/-- When beta and J are positive, the positive s shift makes U positive. -/','/-- The positive s shift makes U positive for every natural beta and J. -/')
m=once(m,'theorem scale_pos (beta : V) (v : Fin 14 → V)\n    (hb : 0<beta) (hJ : 0<v 0) : 0<scale beta v := by','theorem scale_pos (beta : V) (v : Fin 14 → V) : 0<scale beta v := by')
m=once(m,'(hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta) (hJ : 0<v 0)\n    (hz : InternalZero','(hbeta : (p 0 : DiffRing V)=ι beta)\n    (hz : InternalZero')
m=once(m,'(scale_pos beta v hb hJ) hzNat','(scale_pos beta v) hzNat')
r=s['root']
r=once(r,'conditional on the explicit represented positive beta\nand positive J hypotheses used by the signed quotient client. No positivity\nof gamma or sign of Dstar, nor K0/MC/MF representation, is assumed.', 'conditional only on the represented natural beta hypothesis used by the\nsigned quotient client. No positivity of beta, J or gamma, no sign of Dstar,\nand no K0/MC/MF representation is assumed.')
r=once(r,'(hbeta : (p 0 : DiffRing V)=ι beta) (hb : 0<beta) (hJ : 0<v 0)\n    (hz : InternalZero','(hbeta : (p 0 : DiffRing V)=ι beta)\n    (hz : InternalZero')
r=once(r,'signed_quotient_of_zero_w_zero p beta v hbeta hb hJ hz hw','signed_quotient_of_zero_w_zero p beta v hbeta hz hw')
d=s['div']
d=once(d,'import Natural79ZeroWJPos\n','')
d=once(d,'open Natural79ZeroWJPosDraft\n','')
d=once(d,'(hq : 2≤Q)','(hq : 1≤Q)')
d=once(d,'(by simp : (0:V)<2) hq','(by simp : (0:V)<1) hq')
d=once(d,'/-- A literal 79 zero cannot have w=0 under represented natural K0 and\nrepresented positive beta. This client assumes neither gamma positivity nor\nany representation or bound for MC and MF. All imported source drafts and\nthis theorem remain unelaborated. -/', '/-- A literal 79 zero cannot have w=0 under represented natural beta.\nK0, MC and MF are arbitrary integer ports; beta and J may be zero.\nAll imported source drafts and this theorem remain unelaborated. -/')
d=once(d,'(p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)\n    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)\n    (hb : 0<beta) (hz : InternalZero (P79NaturalForcedW.graph p).output v)\n    (hw : v 6=0) : False := by\n  have hJ : 0<v 0 := J_pos_of_zero_w_zero p K v hK hz hw\n  have hsigned := signed_dvd_three_square_of_zero_w_zero p beta v hbeta hb hJ hz hw\n  have hnatural := natural_dvd_three_square (q beta v) (y beta v) hsigned\n  have hprod : 1≤v 0*beta := pos_iff_one_le.mp (mul_pos hJ hb)\n  have hq : 2≤q beta v := by dsimp [q]; nlinarith',
 '(p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)\n    (hbeta : (p 0 : DiffRing V)=ι beta)\n    (hz : InternalZero (P79NaturalForcedW.graph p).output v)\n    (hw : v 6=0) : False := by\n  have hsigned := signed_dvd_three_square_of_zero_w_zero p beta v hbeta hz hw\n  have hnatural := natural_dvd_three_square (q beta v) (y beta v) hsigned\n  have hq : 1≤q beta v := by dsimp [q]; simp')
d=once(d,'/-- The target positive-w statement for any ports satisfying the explicit\nbeta and K0 representations and positive-beta hypothesis. -/','/-- Positive w for any literal zero with represented natural beta. -/')
d=once(d,'(p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)\n    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)\n    (hb : 0<beta) (hz : InternalZero (P79NaturalForcedW.graph p).output v) : 0<v 6 := by',
 '(p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)\n    (hbeta : (p 0 : DiffRing V)=ι beta)\n    (hz : InternalZero (P79NaturalForcedW.graph p).output v) : 0<v 6 := by')
d=once(d,'zero_w_impossible p beta K v hbeta hK hb hz hw','zero_w_impossible p beta v hbeta hz hw')
e=s['end']
e=once(e,'  have hb : 0 < (CompactFixedBeta.betaNat : V) :=\n    Natural82EndpointDraft.symbolic_beta_positive\n  have hK : (CompactSymbolicModelIff.p 1 : DiffRing V)=ι (paramKernel rho : V) :=\n    StrictK0SymbolicDraft.port_one_representation\n','')
e=once(e,'      (CompactFixedBeta.betaNat : V) (paramKernel rho : V) v hbeta hK hb hv)',
 '      (CompactFixedBeta.betaNat : V) v hbeta hv)')
outputs={'Natural79ZeroWMainNorm.lean.src':m,'Natural79ZeroWRootCut.lean.src':r,'Natural79ZeroWDivisibility.lean.src':d,'Natural79Endpoint.lean.src':e}
# Exact q and Y graph cuts, with independent polynomial leaves J, beta, s.
g=json.loads(s['graph']);rows={n:(op,x,y) for n,op,x,y in g['source']}
def con(n):return {} if n==0 else {():n}
def var(n):return {(n,):1}
def add(a,b):
 o=dict(a)
 for k,v in b.items():o[k]=o.get(k,0)+v
 return {k:v for k,v in o.items() if v}
def mul(a,b):
 o={}
 for k,v in a.items():
  for l,w in b.items():
   x=tuple(sorted(k+l));o[x]=o.get(x,0)+v*w
 return {k:v for k,v in o.items() if v}
@lru_cache(None)
def ev(n):
 if type(n)==int:return con(n)
 if n not in rows:return var(n)
 op,x,y=rows[n];a,b=ev(x),ev(y)
 return mul(a,b) if op=='*' else add(a,b) if op=='+' else add(a,{k:-v for k,v in b.items()})
q=add(con(1),mul(var('n_J'),var('beta')));Y=mul(mul(mul(q,q),q),add(var('n_s'),con(1)))
assert ev('q')==q and ev('Y')==Y and ev('U')==mul(Y,mul(q,q))
# Exact ring identity behind the q>=1 size inequality; each difference on
# the right is nonnegative under Y>=q^3 and q^3>=q^2.
def sub(a,b):return add(a,{k:-v for k,v in b.items()})
Q=var('Q'); W=var('W'); Q2=mul(Q,Q); Q3=mul(Q2,Q)
left=sub(add(mul(con(4),W),con(3)),mul(con(3),Q2))
right=add(add(mul(con(4),sub(W,Q3)),mul(con(4),sub(Q3,Q2))),add(Q2,con(3)))
assert left==right
assert 'import Natural79ZeroWJPos' not in m and 'import Natural79ZeroWJPos' not in d
assert all(x not in d for x in ('hK','hJ','(hb :','2≤Q','2≤q beta v'))
assert sys.argv==[sys.argv[0]]
for n,t in outputs.items():assert (P/'source'/n).read_text()==t,n
print(json.dumps({'scope':'deterministic source edits and exact q/Y/U graph cuts; not Lean or provider verification',
 'pinned_inputs':{k:{'path':p,'sha256':h} for k,(p,h) in sorted(paths.items())},
 'inert_snapshots':{n:sha(t.encode()) for n,t in sorted(outputs.items())},
 'natural79_beta_representation_only':True,'new_axiom_reports_unexecuted':True,
 'lean_elaboration':False},sort_keys=True,indent=2))
