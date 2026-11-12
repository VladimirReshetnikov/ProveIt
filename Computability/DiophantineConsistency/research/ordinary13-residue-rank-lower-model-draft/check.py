#!/usr/bin/env python3
"""Bounded scalar controls and source pins; no Lean proof."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-rank-lower-model-draft/ResidueRankLower.lean.src': '86fd995a873fedeeeaa79a2a476276870a4a1be26bfc0a273ce052600e941b2f', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src': '422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805', 'research/ordinary13-residue90-norm-model-draft/check.py': '7bd046c946b2ab60d2f9157dfec9cfb98b3b4da296489b97f6d93607077dd16d', 'research/ordinary13-residue90-norm-model-draft/receipt.json': 'df70467acf2a7671cd1059407d0da5e084ac7203860774053efbeb4545b015dd', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean': '0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
p=D/'research/ordinary13-residue90-norm-model-draft'
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes()
s=(P/'ResidueRankLower.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['scalar_rank_at_least_40','graph_rank_at_least_40','graph_rank_at_least_26','(hgap : F+alpha<q)','(5:V)','(8:V)']:
 assert x in s,x
cases=0;lowest=None
for q in range(3,26):
 for F in range(1,q):
  for a in range(1,q-F):
   for MC,MF,J in [(0,0,0),(1,2,3)]:
    R=((q-1)*(q-F)+a)*(q*q-1)+(MC+q*MF)*J
    assert R>=40;lowest=R if lowest is None else min(lowest,R);cases+=1
assert lowest==40
print(json.dumps({'scope':'bounded source and scalar controls, no Lean','pinned_files':len(pins),'finite_cases':cases,'minimum_in_box':lowest,'graph_gap_and_provider_proof_remain_open':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
