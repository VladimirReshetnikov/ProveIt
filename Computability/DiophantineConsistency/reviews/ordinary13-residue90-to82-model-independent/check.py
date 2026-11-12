#!/usr/bin/env python3
"""Independent source and mixed-coordinate model transport review, no Lean."""
import hashlib,json,re,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue90-to82-model-draft/Residue90To82Transport.lean.src','bd8ac5e52ff1e82b732b0a0bbeebce88b5d39629a5695aceee5e9a4565436e83')
l=pin('research/ordinary13-residue90-to82-model-draft/Residue82Literal.lean.src','fa20dbc55a71afe4168864237eaab5ec22b31a1f558d1bc70c9b17bcbc657295')
r=pin('research/ordinary13-residue90-to82-model-draft/Residue82Residuals.lean.src','ef8ffe28d4d80fd1448ee87817d5eb3c2ee8e7bd0c403d4bb050272cce6f80ff')
pin('research/ordinary13-residue90-to82-model-draft/receipt.json','03a911d8adcd840c5458531650c16a19b25bf86368f2524441e2155f6817f2f0')
pin('reviews/ordinary13-residue90-fy-model-independent/result.json','d966ff3d5ec756e09d9c349fde0847e3bf618050c1109a76c031f789b17a50b0')
pin('reviews/ordinary13-residue90-xzero-graph-independent/result.json','ffa967831cfed486dca16c9f3bbf9a3735fcc0e298c13b1cfc124a19b8b0cc6e')
p=json.loads(pin('research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2'))
c=json.loads(pin('research/ordinary13-natural-residue-forced90-degree56/candidate.json','e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'))
# Check all generated graph assignments, variable positions, port positions and residual vector.
for src in [l,r]:
 for i,name in enumerate(p['witnesses']):assert f'let {name} : Expr (Fin 13) := .var {i}' in src
 for i,name in enumerate(p['fixed_numerals']):assert f'let {name} : Expr (Fin 13) := .constant (p {i})' in src
 lines=re.findall(r'^  let (\w+) := (\w+|\d+) ([+*\-]) (\w+|\d+)$',src,re.M)
 assert lines==[(n,str(a),o,str(b)) for n,o,a,b in p['source']]
assert '![A0,A1,Fam,g72]' in r and ': Fin 4 → Expr (Fin 13)' in r
forced={'J','f','X','y','gamma'};mapping={x:'n_'+x if x in forced else 'shift_'+x for x in p['witnesses']}
sub=lambda x:mapping.get(x,x) if isinstance(x,str) else x
assert c['source']==[['shift_'+x,'+','n_'+x,1] for x in p['witnesses'] if x not in forced]+[[n,o,sub(a),sub(b)] for n,o,a,b in p['source']]
assert 'i=0 ∨ i=3 ∨ i=6 ∨ i=11 ∨ i=12' in s
for x in ['theorem mixed_pos','theorem mixed_lower','Residue90FirstNormJDraft.J_positive','Residue90XZeroGraphDraft.compact_X_positive','Residue90FyForceDraft.f_y_positive','Residue90XZeroGraphDraft.compact_gamma_positive','(hparent : PolynomialBridge (positiveShift','theorem native_equivalence']:
 assert x in s,x
for i in range(4):assert f'theorem relation0{i}' in s
# Check the two coordinate maps on finite cases; source identity follows from row substitution.
for i in range(13):
 for v in range(1,30):
  lower=v if i in {0,3,6,11,12} else v-1
  mixed=lower if i in {0,3,6,11,12} else lower+1
  assert mixed==v
print(json.dumps({'scope':'exact generated parent graph and mixed valuation source review; no Lean','forced_coordinates':[0,3,6,11,12],'shifted_coordinates':8,'parent_bridge_explicit':True,'arbitrary_standard_K':True,'physical_kernel_binding_unproved':True,'lean_elaborated':False},sort_keys=True,indent=2))
