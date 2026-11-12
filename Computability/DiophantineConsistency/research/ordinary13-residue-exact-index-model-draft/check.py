#!/usr/bin/env python3
"""Bounded source and discriminant controls; no Lean execution."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-exact-index-model-draft/ResidueExactIndexModel.lean.src': 'dc941fd8914795ac46f513f45979ef7c69c22a6d1be4dc332605f1ddb7a3a79a', 'research/ordinary13-residue-main-congruence-model-draft/ResidueMainCongruence.lean.src': 'c92cbbca34371870b01f03042de0a4a024bd56a6175d909c43b6887736700ce8', 'research/ordinary13-residue-main-congruence-model-draft/check.py': 'be56af156340a50b859237b4efd8ce50c209a5114869f16eaf0dd5692cb509bc', 'research/ordinary13-residue-main-congruence-model-draft/receipt.json': 'ac2ce7760b3fcc5448f507b19cb7a0620d0ae113500f624b6893e517dac4e168', 'research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src': '0b69fb042a913232ef9f4a92757107f60d8a590f855176134587939012b1b93b', 'research/ordinary13-residue-first-index-model-draft/check.py': '326f626d2d09dc43ba08c11849e912a5fe8830f7e85729b58d0f94f1493ebf20', 'research/ordinary13-residue-first-index-model-draft/receipt.json': '0a6fa5d8a83af0132714f600742bccc91c78f9a3e65fe96b0aef3cae0ea9ef1b', 'Lean/DiophantineConsistency/Compact44/P72Exact.lean': 'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3', 'Lean/DiophantineConsistency/ArithmeticPellClassification.lean': '77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78', 'Lean/DiophantineConsistency/ArithmeticPellHalfIndex.lean': '7703193660d8ae98408d1ec3a83f6f8811927252e739bb7af18dbafb833a8877', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet in ['ordinary13-residue-main-congruence-model-draft','ordinary13-residue-first-index-model-draft']:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes(),packet
s=(P/'ResidueExactIndexModel.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['main_index_of_natural_norm','ArithmeticPellClassification.solution_index','exact_indices_of_actual_graph','early_index_of_actual_graph','P72Exact.indices_ordinary','(hR26 : 26≤rank p v)','(hmy :','(hg :','(hstrong :','(haux :']:
 assert x in s,x
assert 'P72Exact.exact_ordinary' not in s and 'core.z' not in s
cases=0
for a in range(101):
 for c in range(21):
  delta=(a+1)*(a+3);assert delta==(3+4*a)+a*a
  assert (a+2)**2==delta+1
  for g in (0,1,2,7):
   assert (g*g==1+delta*c*c)==(g*g==1+((3+4*a)+a*a)*c*c);cases+=1
print(json.dumps({'scope':'bounded source and discriminant controls; no Lean','pinned_files':len(pins),'finite_discriminant_cases':cases,'strong_aux_main_index_R26_explicit':True,'later_Bezout_projection_open':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
