from pathlib import Path
from hashlib import sha256
import json,random
p=Path('research/ordinary13-positive81-calibration-model-draft')
fs=[p/'Positive81Calibration.lean.src',p/'Positive81ExactIndexCut.lean.src',p/'README.md',
Path('research/ordinary13-positive81-to83-model-draft/Positive81To83Transport.lean.src'),
Path('research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src'),
Path('research/ordinary13-eta-zero-growth-model-draft/EtaZeroGrowth.lean.src'),
Path('Lean/DiophantineConsistency/Compact44/P72Exact.lean'),
Path('research/ordinary13-positive81-to83-model-gap-audit/README.md')]
s=[f.read_text() for f in fs]
for x in ['def ExactIndexCut','def OrientedMainCut','theorem prototype_power',
 'EtaNaturalGraphEarlyIndexDraft.compact_early_index','hexact n w hn hny hks hnmod',
 'EtaZeroGrowthDraft.power','theorem rank_qsquare','theorem prototype_rank_qsquare',
 'le_of_lt (lt_exp _)','theorem calibration81',
 'Positive81To83TransportDraft.prototype_zero_of81','theorem original81_coordinates','theorem calibration81_original']:
 assert x in s[0],x
for x in ['theorem exact_pair','P72Exact.indices_ordinary','(heta : 0<eta)',
 '(hstrong :','(haux :','m=R ∧ 2*n=R+1']:
 assert x in s[1],x
assert '(positiveShift' not in s[0] and 'zero83_to81' not in s[0]
rng=random.Random(818185);n=0
for _ in range(400):
 q=rng.randrange(2,12);R=rng.randrange(q*q,200)
 assert q*q<=R<2**R
 n+=1
rank_cases=0
for q in range(3,35):
 for F in range(1,q):
  for alpha in range(1,q-F):
   A=(q-1)*(q-F)+alpha;R=A*(q*q-1)
   assert A>=2 and q*q<=R
   rank_cases+=1
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'explicit_exact_index_and_main_cuts':True,'same_early_n_w_used':True,
 'rank_to_exponential_controls':n,'positive_gap_rank_controls':rank_cases,'lean_executed':False,
 'status':'unelaborated; exact-index, main root, rank and all provider obligations remain open'},sort_keys=True,indent=2))
