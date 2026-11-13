from pathlib import Path
from hashlib import sha256
import json,random
p=Path('research/ordinary13-eta-natural-rank-index-model-draft')
fs=[p/'EtaNaturalRankIndex.lean.src',p/'README.md',
Path('research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src'),
Path('research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src'),
Path('research/ordinary13-residue-compact-qbound-model-draft/ResidueCompactQBound.lean.src'),
Path('research/ordinary13-eta-zero-early-congruence-model-draft/EtaZeroEarlyCongruence.lean.src'),
Path('research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src')]
s=[f.read_text() for f in fs]
for x in ['theorem rank_at_least_26','(hq : 6≤q p v)','theorem compact_rank_at_least_26',
 'compact_q_at_least_47','theorem compact_early_index_of_norms','(hfirst :','(hmain :',
 'EtaNaturalXPositiveDraft.X_positive','EtaNaturalGapRankDraft.compact_rank_window',
 'EtaZeroEarlyCongruenceDraft.early_index_of_actual_carrier']:
 assert x in s[0],x
assert 'by omega' not in s[0]
assert '(hR26 : 26 ≤ R)' in s[6]
R=random.Random(6031);count=nogap=0
for _ in range(4000):
 q=R.randrange(6,80);F=R.randrange(1,120);alpha=R.randrange(1,20)
 MC=R.randrange(20);MF=R.randrange(20);J=R.randrange(20)
 A=max(q-1,0)*max(q-F,0)+alpha
 rr=A*max(q*q-1,0)+(MC+q*MF)*J
 assert A>=1 and q*q-1>=26 and rr>=26
 if F+alpha>=q:nogap+=1
 count+=1
assert nogap>0
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'rank_controls':count,'controls_without_positive_gap':nogap,'lean_executed':False,
 'status':'unelaborated; prototype norm, model ports and providers remain open'},sort_keys=True,indent=2))
