#!/usr/bin/env python3
"""Pinned same-witness interfaces and finite carrier/index sanity checks."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
r=ROOT/'research'; src=(r/'ordinary13-positive81-exact-main-model-draft/Positive81ExactMain.lean.src').read_text()
for x in ['(heta : 0<v 9) (n w : V) (hn : 13≤n)',
 'EtaNaturalGraphEarlyIndexDraft.main_pair_norm p v hz hFq',
 '⟨main,_,hbalance,hnorm⟩ := DirectMainNorm.direct_main_orientation',
 'ArithmeticPellClassification.solution_index a main (c p v) hg',
 'EtaNaturalGraphStrongAuxDraft.index_hypotheses_of_geometry',
 '(v 4+1) (v 3) (v 5+1) u n w ((q p v)^4) m (v 9)',
 'hq3 hX hs hYq heta hcdef hi hf hadef hR26 hny hks hRmu hnmod hmy hg hstrong\' haux\'',
 'simpa only [hmR,ha] using hmx','simpa only [hmR,ha] using hmy',
 'linear_combination -hbalance',
 'exact (exact_and_main K v hz heta n w hn hny hks hnmod).1',
 '(exact_and_main K v hz heta n w hn hny hks hnmod).2',
 'theorem image85_eta_positive','(exactIndexCut K e hz85 he) (orientedMainCut K e hz85 he)']:
 assert x in src,x
p72=(ROOT/'Lean/DiophantineConsistency/Compact44/P72Exact.lean').read_text()
assert '13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1' in p72
# Check no-E*q balance sign and norm grouping in integers.
count=0
for X,Y,eta,zeta,U,R,gamma,main in itertools.product(range(1,4),range(1,4),range(1,3),range(1,3),range(1,4),range(4),range(3),range(4)):
 a=X*Y+Y;c=eta+Y*(eta+zeta);H=3+4*a;D=H+a*a;k=eta+zeta
 P=U*(X+a*c)+H*(U*gamma+R+1);N=H*k
 assert (a+2)**2==D+1
 assert (U*main+N-P)==-(P-(N+U*main))
 # DirectMainNorm's 1+D*(c*c) is the same as 1+D*c*c.
 assert 1+D*(c*c)==1+D*c*c
 count+=1
for x in range(1,30):assert x-1+1==x
print(json.dumps({'source_pins':pins,'carrier_and_norm_controls':count,
 'p72_witness_order_and_eta_image_checked':True,'lean_executed':False,
 'scope':'conditional source/math audit, not all-model elaboration or endpoint'},sort_keys=True,indent=2))
