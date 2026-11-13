#!/usr/bin/env python3
"""Bounded source and arithmetic checks, not a Lean proof."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]; HERE=Path(__file__).resolve().parent
PINS={
 'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f',
 'research/current2011-sheared72-46-proof-draft/ShearDraft.lean':'a479640aa326cb2190d530bb806d199f29c77796acd8f93edaffe609e5a8af2a',
 'Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean':'afc99ad41536f55e0f467581e4fbdbd5308036f93b6e3e10b1a5d2f1c113de4a',
 'Lean/DiophantineConsistency/Carrier65.lean':'be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154',
 'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',
 'research/current2011-shear-v-not-one-order-draft/ShearOrder.lean.src':'cf261c518f55d885246c3cad418a5da7981d4ea54f9548ebece200df3a39ed99',
}
for name,h in PINS.items():
 if hashlib.sha256((ROOT/name).read_bytes()).hexdigest()!=h: raise RuntimeError('source pin changed: '+name)
index=(ROOT/'Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean').read_text()
if 'theorem ordinary_first_indices' not in index or '2*R<k*Y+eta' not in index: raise RuntimeError('missing index interface')
parent=json.loads((ROOT/'research/current2011-ordinary71-60-candidate/polynomial.json').read_bytes())
child=json.loads((ROOT/'research/current2011-sheared72-46-candidate/polynomial.json').read_bytes())
for graph in (parent,child):
 rows={x[0]:x for x in graph['source']}
 if rows.get('V')!=['V','-','f2inner','c'] or rows.get('f2inner')!=['f2inner','*','f2','cTminusR'] or rows.get('cTminusR')!=['cTminusR','-','cT','R']:
  raise RuntimeError('carrier row mismatch')
if ['y_old','+','V','y'] not in child['source']: raise RuntimeError('shear row mismatch')
examined=0; shear_cases=0
for c in range(1,10):
 for f in range(2,8):
  for T in range(1,6):
   for rank in range(-5,8):
    if 2*rank<c:
     examined+=1
     if f*f*(c*T-rank)-c==1: raise RuntimeError('order contradiction control failed')
for A in range(1,8):
 for V in range(-8,9):
  for y in range(1,9):
   if A*(V*V-y*y)+y*y==1 and V!=1:
    shear_cases+=1
    if y<=V: raise RuntimeError('positive shear control failed')
if 4*(3-2)-3!=1 or not 2*2>=3: raise RuntimeError('half-boundary control failed')
print(json.dumps({'scope':'bounded arithmetic and source pins only; no Lean or graph-zero proof',
 'order_cases':examined,'shear_unit_cases':shear_cases,'rank_bound_negative_control':True,
 'source_sha256':PINS['research/current2011-shear-v-not-one-order-draft/ShearOrder.lean.src']},indent=2,sort_keys=True))
