#!/usr/bin/env python3
"""Read-only source pin/marker audit; no Lean invocation."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PINS={
 'research/current2011-shear-forward-norm-order-draft/ForwardNormOrder.lean.src':'de67ebbb8699e8f43f28f8db6caca0da8edaed522503e4ba9a98f4d12b7a5b2d',
 'research/current2011-shear-v-not-one-order-draft/ShearOrder.lean.src':'cf261c518f55d885246c3cad418a5da7981d4ea54f9548ebece200df3a39ed99',
 'research/current2011-ordinary71-60-generic/OrdinarySphere7160Generic.lean':'5808bcc7f662ff319ad6c64811260e216739888a7d4a8d89c68390d2561f9bae',
 'research/current2011-ordinary71-60-literal/OrdinarySphere7160Literal.lean':'554fa13261dcb4f9535764871b4833d0b6182fab9503bfa27b3bc5f88d64d84a',
 'research/current2011-spheres-fresh-base/FreshCarrierSpheres.lean':'a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5',
}
for path,h in PINS.items():
 if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=h: raise RuntimeError('pin changed: '+path)
MARKERS={
 'research/current2011-ordinary71-60-generic/OrdinarySphere7160Generic.lean':['def value71','theorem zero_iff94','auxiliary_ne_zero','square_aux_ne_neg_one'],
 'research/current2011-ordinary71-60-literal/OrdinarySphere7160Literal.lean':['def value71','theorem eval_expression'],
 'research/current2011-spheres-fresh-base/FreshCarrierSpheres.lean':['theorem first_ne_zero','theorem auxiliary_ne_zero','theorem square_ge_one','theorem square_aux_ne_neg_one','theorem c_pos'],
 'research/current2011-shear-forward-norm-order-draft/ForwardNormOrder.lean.src':['theorem value_positive_shear','theorem literal_positive_shear','(hhalf :','graph_carrier_ne_one','positive_shear'],
}
for path,need in MARKERS.items():
 t=(ROOT/path).read_text()
 if any(s not in t for s in need): raise RuntimeError('source marker missing: '+path)
print(json.dumps({'scope':'source pins and interface markers; draft unelaborated',
 'pinned_files':len(PINS),'signed_half_bound_explicit':True,'natural_witness_constructed':False},indent=2,sort_keys=True))
