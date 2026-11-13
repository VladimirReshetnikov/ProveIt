#!/usr/bin/env python3
"""Pinned graph substitution, signed-divisor identity and finite sanity controls."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for f,h in pins.items():assert hashlib.sha256((ROOT/f).read_bytes()).hexdigest()==h,f
r=ROOT/'research'
paths=['ordinary13-natural-unit-product89/candidate.json','ordinary13-natural-unit-product88/candidate.json','ordinary13-natural-forced-gamma87/candidate.json','ordinary13-natural-forced-w86/candidate.json','ordinary13-eta-zero-graph-adapter-audit/prototype.json']
g=[json.loads((r/p).read_text()) for p in paths]
assert [len(x['source']) for x in g]==[89,88,87,86,85]
for parent,child,name,var in zip(g,g[1:],['J','gamma','w','eta'],['n_J','n_gamma','n_w','n_eta']):
 assert parent['witnesses']==child['witnesses'] and parent['fixed_numerals']==child['fixed_numerals']
 assert [[var if x==name else x for x in row] for row in parent['source'] if row!=[name,'+',var,1]]==child['source']
assert g[0]['witnesses'][3]=='n_f' and g[0]['witnesses'][11]=='n_y'
for mask in range(16):
 v=list(range(13));v[0]=mask
 original=(v[3],v[11])
 for ix in (0,12,6,9):v[ix]+=1
 assert (v[3],v[11])==original
# Verify the exact orientation of linear_combination -haux at y=0:
# aux-defect=0 - D*(f²−1)*(0−z²)−1, goal-defect=1−D*((f²−1)*z²).
count=0
for D,f,z in itertools.product(range(3,9),range(7),range(-6,7)):
 aux=0-D*(f*f-1)*(0-z*z)-1
 goal=1-D*((f*f-1)*z*z)
 assert goal==-aux
 if f==0:assert -(D*(f*f-1))>0
 # D cannot divide 1 as a natural, independently of the sign of the witness.
 assert 1%D != 0
 count+=1
src=(r/'ordinary13-natural89-direct-fy-model-draft/Natural89DirectFY.lean.src').read_text()
for x in ['EtaNaturalGraphStrongAuxDraft.ordinary_strong',
 'EtaNaturalStrongAuxDraft.f_positive_of_strong','EtaNaturalUnitBridgeDraft.signed_norms',
 'EtaNaturalGraphStrongAuxDraft.field_y','EtaNaturalGraphNormsDraft.field_delta',
 'EtaNaturalGraphStrongAuxDraft.field_f','linear_combination -haux',
 'Trace75IntegralTransport.natural_dvd_of_signed D 1 hunit\'',
 'Natural89Positive80TransportDraft.DirectFY K']:
 assert x in src,x
print(json.dumps({'source_pins':pins,'graph_row_counts':[89,88,87,86,85],
 'four_exact_forward_substitutions':True,'signed_divisor_controls':count,
 'lean_executed':False,'scope':'conditional source review; no model proof or provider authentication'},sort_keys=True,indent=2))
