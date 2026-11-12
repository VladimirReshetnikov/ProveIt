#!/usr/bin/env python3
"""Pinned source interfaces and finite scalar rank controls; no Lean."""
from pathlib import Path
import hashlib,itertools,json,re
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for n,h in pins.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
r=ROOT/'research';s=(r/'ordinary13-positive81-calibration-model-draft/Positive81Calibration.lean.src').read_text()
t=(r/'ordinary13-positive81-calibration-model-draft/Positive81ExactIndexCut.lean.src').read_text()
for needle in ['def ExactIndexCut','∀ n w : V, 13≤n','2*ycoord n',
 'k v=2*n+4*(X p v*Y p v*Y p v)*w',
 '(2*n)%((q p v)^4)=rank p v+1 → 2*n=rank p v+1',
 'def OrientedMainCut','xcoord (rank p v)','ycoord (rank p v)',
 'U*main+H*k v=U*(X p v+a*c p v)+H*(U*v 12+rank p v+1)',
 'EtaNaturalGraphEarlyIndexDraft.compact_early_index K v hz',
 'hexact n w hn hny hks hnmod','EtaZeroGrowthDraft.power',
 '(v 7+1) (v 6) w','hny.symm hmainx hmainy hindex hcar',
 'Positive81To83TransportDraft.prototype_zero_of81',
 '(hexact : ExactIndexCut (ports K) (Positive80To81TransportDraft.image85 v))',
 '(hmain : OrientedMainCut (ports K) (Positive80To81TransportDraft.image85 v))',
 'prototype_rank_qsquare K v hz','lt_exp _',
 'theorem original81_coordinates','theorem calibration81_original',
 '(1+v 0*(ports K 0:V))*v 6']:
 assert needle in s,needle
for needle in ['theorem exact_pair','P72Exact.indices_ordinary q X Y k R g c a y0 i f T u n w mu m eta',
 'hny hks hRmu hnmod hmy hg hstrong haux','m=R ∧ 2*n=R+1']:
 assert needle in t,needle
# Independent finite controls for the weaker scalar lemma q²≤R.
count=0
for q,F,alpha,J,MC,MF in itertools.product(range(2,13),range(1,13),range(1,5),range(4),range(3),range(3)):
 if F>=q:continue
 A=(q-1)*(q-F)+alpha;Q=q*q-1;R=A*Q+(MC+q*MF)*J
 assert A>=2 and Q>=1 and q*q<=2*Q<=A*Q<=R
 count+=1
# Positive 81 coordinates lower at the ten shifted positions, then the four
# actual forward shifts restore positions 0,12,6,9.
for v in itertools.product(range(1,4),repeat=3):
 arr=[2]*13;arr[3],arr[8],arr[11]=v
 lower=[x if i in (3,8,11) else x-1 for i,x in enumerate(arr)]
 for i in (0,12,6,9):lower[i]+=1
 assert lower==[arr[i]-1 if i in (1,2,4,5,7,10) else arr[i] for i in range(13)]
print(json.dumps({'source_pins':pins,'rank_qsquare_finite_controls':count,
 'same_first_index_and_quotient_source_checked':True,'positive81_map_controls':27,
 'lean_executed':False,'scope':'conditional source audit; cuts remain assumptions and no model/provider proof'},sort_keys=True,indent=2))
