from pathlib import Path
from hashlib import sha256
import json,random
p=Path('research/ordinary13-positive81-exact-main-model-draft')
fs=[p/'Positive81ExactMain.lean.src',p/'README.md',
Path('research/ordinary13-positive81-calibration-model-draft/Positive81Calibration.lean.src'),
Path('research/ordinary13-positive81-calibration-model-draft/Positive81ExactIndexCut.lean.src'),
Path('research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src'),
Path('research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src'),
Path('research/ordinary13-eta-natural-norm-large-k-draft/EtaNaturalNormLargeK.lean.src'),
Path('research/ordinary13-eta-natural-auxiliary-draft/AuxGeometryEtaNatural.lean.src'),
Path('Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean'),
Path('Lean/DiophantineConsistency/ArithmeticPellClassification.lean')]
s=[f.read_text() for f in fs]
for x in ['theorem exact_and_main','(heta : 0<v 9)','(n w : V)','(hny :','(hks :','(hnmod :',
 'EtaNaturalGraphEarlyIndexDraft.main_pair_norm','DirectMainNorm.direct_main_orientation',
 'ArithmeticPellClassification.solution_index','EtaNaturalNormLargeKDraft.large_first_ordinate',
 'AuxGeometryEtaNaturalDraft.geometry_of_large_k','EtaNaturalGraphStrongAuxDraft.index_hypotheses_of_geometry',
 'Positive81ExactIndexCutDraft.exact_pair','theorem exactIndexCut','theorem orientedMainCut',
 'theorem image85_eta_positive','theorem calibration81_original']:
 assert x in s[0],x
assert 'zero83_to81' not in s[0]
assert 'EtaNaturalGraphEarlyIndexDraft.compact_early_index K v hz' in s[0]
assert 'linear_combination -hbalance' in s[0]
assert 'm=R ∧ 2*n=R+1' in s[3]
rng=random.Random(81815)
for _ in range(500):
 q=rng.randrange(2,15);X=rng.randrange(1,20);Y=rng.randrange(1,20);eta=rng.randrange(1,10);zeta=rng.randrange(1,10)
 U=Y*q*q;k=eta+zeta;c=eta+Y*k;a=X*Y+Y;H=3+4*a
 gamma,R,main=(rng.randrange(20) for _ in range(3))
 P=U*(X+a*c)+H*(U*gamma+R+1);N=H*k
 balance=P-(N+U*main);target=U*main+H*k-U*(X+a*c)-H*(U*gamma+R+1)
 assert target==-balance and (a+2)**2==((3+4*a)+a*a)+1
 vals=[rng.randrange(1,20) for i in range(13)]
 down=[x if i in {3,8,11} else x-1 for i,x in enumerate(vals)]
 for i in [0,12,6,9]:down[i]+=1
 assert down[9]==vals[9]
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'same_oriented_main_used':True,'carrier_defect_and_eta_controls':500,
 'lean_executed':False,'status':'unelaborated; model graph proofs and provider ancestry remain open'},sort_keys=True,indent=2))
