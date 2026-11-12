#!/usr/bin/env python3
"""Check literal main-factor formulas and model-source signatures; no Lean."""
from pathlib import Path
import hashlib,json,random,re,sys
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent;D=P.parents[1];L=D/'Lean/DiophantineConsistency'
pins={
 'client':(P/'Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009'),
 'jpos':(D/'research/ordinary14-natural79-zero-w-jpos-draft/Natural79ZeroWJPos.lean','f1cf89c29eebe2259069dd26fd66d8cece75d48374358cc95ab9cc1ba83a2f0a'),
 'atoms':(D/'research/ordinary14-natural79-factor-residues-draft/Natural79ResidueShapes.lean','b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38'),
 'units':(D/'research/ordinary14-natural79-factor-residues-draft/Natural79ConcreteUnits.lean','253421a5ac864a94a9926472d9c469c2997d6581cded0aaa3fda27b2830d118d'),
 'graphsrc':(D/'research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36'),
 'graph':(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'),
 'patterns':(D/'research/ordinary14-74-factor-residues-draft/FactorResidues74.lean','368e6e5f3db5693db859fdc85a9441f0d6378969563eec289c2c121e6b4b1d60'),
 'magnitude':(L/'Compact44/ReducedNormSigned.lean','c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c'),
 'quotient':(L/'ArithmeticAdaptiveQuotients2011.lean','40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884')}
s={}
for n,(p,h) in pins.items():
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,n;s[n]=b.decode()
g=json.loads(s['graph']);assert g['operations']==len(g['source'])==79
start='  let n_J : Expr (Fin 14) := .var 0'; assert s['graphsrc'].count(start)==s['atoms'].count(start)==1
assert s['graphsrc'].split(start,1)[1].split('  -- END LITERAL GRAPH',1)[0]==s['atoms'].split(start,1)[1].split('  ⟨U,a,c,Dstar,I,V⟩',1)[0]
assert 'theorem main_shape' in s['atoms'] and 'mainPattern (atoms p).U (atoms p).a (atoms p).c (atoms p).Dstar' in s['atoms']
assert '1+(d*d-u*u*(1+((3+4*a)+a*a)*(c*c)))' in s['patterns']
assert '(pairEval (P79NaturalForcedW.graph p).main v).2+1 ∧' in s['units']
assert 'theorem eval_one_of_pair_unit' in s['jpos']
assert 'theorem natural_magnitude_square (x : DiffRing V)' in s['magnitude']
assert '∃ a : V, (x=ι a ∨ x= -ι a) ∧ x*x=ι (a*a)' in s['magnitude']
assert 'theorem scaled_quotient (m z n : V) (hm : 0<m) (h : z*z=m*m*n)' in s['quotient']
for token in ('def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta',
 'q beta v*(q beta v*q beta v)*(v 7+1)',
 'def k (v : Fin 14 → V) : V := (v 9+1)+(v 10+1)',
 '(v 9+1)+y beta v*k v','y beta v*(q beta v*q beta v)',
 '1+(y beta v*y beta v+(4*y beta v+3))*(c beta v*c beta v)',
 'theorem main_eval_cut','theorem atoms_at_zero_w',
 'theorem main_norm_of_zero_w_zero','theorem signed_quotient_of_zero_w_zero',
 '(hbeta : (p 0 : DiffRing V)=ι beta)','(hz : InternalZero (P79NaturalForcedW.graph p).output v) (hw : v 6=0)',
 'Natural79ConcreteUnitsDraft.units_of_zero_w_zero p v hz hw',
 'eval_one_of_pair_unit (P79NaturalForcedW.graph p).main v units.2.1',
 'ReducedNormSigned.natural_magnitude_square D','scaled_quotient (scale beta v) z (normRhs beta v)',
 'rcases hsgn with hp | hn','refine ⟨-ι t'):
 assert token in s['client'],token
for n in ('main_norm_of_zero_w_zero','signed_quotient_of_zero_w_zero'):
 assert f'#print axioms DiophantineConsistency.Natural79ZeroWMainNormDraft.{n}' in s['client']
# Independent finite full-DAG integer checks. w=0, all other witnesses natural;
# K0, MC and MF are arbitrary signed integers, and beta,J are positive.
needed={'F1','Dstar','c','a','U','Y','q'}
for n,op,x,y in reversed(g['source']):
 if n in needed:needed.update(v for v in (x,y) if isinstance(v,str))
rng=random.Random(799)
for _ in range(300):
 e={n:rng.randrange(4) for n in g['witnesses']};e['n_J']=rng.randrange(1,4);e['n_w']=0
 e.update({'beta':rng.randrange(1,4),'K0':rng.randrange(-3,4),'MC':rng.randrange(-3,4),'MF':rng.randrange(-3,4)})
 v=e.copy()
 for n,op,x,y in g['source']:
  if n not in needed:continue
  x=x if type(x) is int else v[x];y=y if type(y) is int else v[y]
  v[n]=x+y if op=='+' else x-y if op=='-' else x*y
 q=1+e['n_J']*e['beta'];Y=q*(q*q)*(e['n_s']+1);k=(e['n_eta']+1)+(e['n_zeta']+1);c=e['n_eta']+1+Y*k;U=Y*q*q
 assert v['q']==q and v['Y']==v['a']==Y and v['c']==c and v['U']==U>0
 assert v['F1']==1+v['Dstar']**2-U**2*(1+(Y*Y+4*Y+3)*c*c)
print(json.dumps({'scope':'pinned graph and source interfaces, finite controls; no Lean or iPRA theorem',
 'pinned_files':len(pins),'graph_rows':len(g['source']),'finite_main_cut_controls':300,
 'both_signed_root_cases_in_source':True,'axiom_reports_not_run':2},sort_keys=True,indent=2))
