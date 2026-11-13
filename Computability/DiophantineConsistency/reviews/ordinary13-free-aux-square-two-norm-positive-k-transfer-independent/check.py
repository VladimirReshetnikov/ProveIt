#!/usr/bin/env python3
"""Independent exact DAG comparison plus unit-factor and port recipe checks."""
import hashlib,json,itertools
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
ind=json.loads((root/'research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text())
free=json.loads((root/'research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text())
assert len(ind['source'])==len(free['source'])==84
assert ind['witnesses'][9:11]==['n_eta','n_k']
assert free['witnesses'][9:12]==['n_eta','n_zeta','n_y2']
assert ind['fixed_numerals']==free['fixed_numerals']
# Full exact ordered trees, compared directly rather than by sample values.
def trees(g,old):
 env={name:('w',j) for j,name in enumerate(g['witnesses'])}
 env.update({name:('p',j) for j,name in enumerate(g['fixed_numerals'])})
 if old:env['n_k']=('+',('w',9),('w',10))
 for name,op,a,b in g['source']:
  a=env[a] if isinstance(a,str) else ('literal',a)
  b=env[b] if isinstance(b,str) else ('literal',b)
  env[name]=(op,a,b)
 return env
x,y=trees(ind,True),trees(free,False)
fields=('qm','q','F','alpha','X','Y','U','C','Bt','ell','Z','G','R','a','H','Delta','Dstar','A0','A1')
for name in fields:assert x[name]==y[name],name
# Product-one extraction: b even implies b²=0 mod 4; b odd means q even,
# hence Y=q³s and ell are 0 mod 4. Check all remaining residue cases.
for b,z,X,s,k in itertools.product(range(4),repeat=5):
 Y=(1+b)**3*s;ell=X*Y*Y*k
 assert (1+z*z-b*b*(1+ell*(ell+k)))%4!=3
for U,a,c,d in itertools.product(range(4),repeat=4):
 assert (1+d*d-U*U*(1+(a*a+4*a+3)*c*c))%4!=3
base=root/'Lean/DiophantineConsistency/Compact44'
for name,token in [('CompactFixedBeta.lean','def betaNat : ℕ := 2^(67*8807)-1'),
 ('CompactSymbolicPorts.lean','![β,K,L,β+H]'),
 ('CompactConcreteMask.lean','range 943 ∪ Ico 983 993'),
 ('CompactListMask.lean','if j=special then B-4 else if j∈S then B-2 else B-1'),
 ('CompactHighPopulation.lean','List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]'),
 ('CompactSymbolicKernelOpaque.lean','r^30+r^62+r^1100+r^2201')]:
 assert token in (base/name).read_text(),name
# Check independently that the source retains the exact nonzero kernel binding.
assert 'abbrev c44 : Fin 4 → ℕ := ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat' in (base/'C44Short15Facts.lean').read_text()
print(json.dumps({'ordered_first_main_and_rank_trees_equal':len(fields),
 'independent_k_substitution':'eta+zeta','parent_outputs_compared':False,
 'negative_first_factor_mod4_cases':1024,'negative_main_factor_mod4_cases':256,
 'compact_beta_K_low_high_recipe_checks':True,
 'full_zero_implies_positive_k_standard_integers':True,
 'model_or_Lean_proof':False,'lean_executed':False},indent=2,sort_keys=True))
