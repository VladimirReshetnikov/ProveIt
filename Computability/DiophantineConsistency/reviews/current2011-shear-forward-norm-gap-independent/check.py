#!/usr/bin/env python3
"""Independent source-interface and finite algebra review; no Lean."""
import hashlib,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear-forward-norm-order-draft/README.md':'1ebb89ae58d39d7d54ed2a90186fd779652a9fdcd34a4d2a7d025922adbe8889',
'research/current2011-shear-forward-norm-order-draft/ForwardNormOrder.lean.src':'de67ebbb8699e8f43f28f8db6caca0da8edaed522503e4ba9a98f4d12b7a5b2d',
'research/current2011-shear-forward-norm-order-draft/check.py':'c0f89ba5d2ad86a0ca43da49b9a2e6195521ab217d10da04fb50a7eb34a1425c',
'research/current2011-shear-forward-norm-order-draft/result.json':'001befafbc778fd5f9cb2171a4a237a3cae7d7434e367d4bbff0fc8f0d9fe2b7',
'research/current2011-shear-positive-gap-representation-draft/README.md':'d9c0f30350ea79bc4b17378508102faca1d76deffbd452364855c36ddd0c277a',
'research/current2011-shear-positive-gap-representation-draft/PositiveGapRepresentation.lean.src':'330544ffaedd3afc061931ace2b0518f3ebd5b855e56516944cc34322033b049',
'research/current2011-shear-positive-gap-representation-draft/check.py':'6c7083ccab9eaea556409f10382334fe110fba7262398f67f6140a613253802a',
'research/current2011-shear-positive-gap-representation-draft/pins.json':'98a7386d69020d3106474f3617c7e4b0441226eeac8fb484267ff4488c7423bf',
'research/current2011-shear-positive-gap-representation-draft/receipt.json':'e09964f315863435216383c0b3b2056dede67820d33689ab1dbcd7522faca0d0',
'research/current2011-ordinary71-60-generic/OrdinarySphere7160Generic.lean':'5808bcc7f662ff319ad6c64811260e216739888a7d4a8d89c68390d2561f9bae',
'research/current2011-ordinary71-60-literal/OrdinarySphere7160Literal.lean':'554fa13261dcb4f9535764871b4833d0b6182fab9503bfa27b3bc5f88d64d84a',
'research/current2011-spheres-fresh-base/FreshCarrierSpheres.lean':'a9e4d44f3ef37f81f192d9d7fa03678eaa53ca5ec216b3257a3a6fa7ab48f6a5',
'research/current2011-shear-v-not-one-order-draft/ShearOrder.lean.src':'cf261c518f55d885246c3cad418a5da7981d4ea54f9548ebece200df3a39ed99',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
def need(b,m):
 if not b:raise RuntimeError(m)
for path,h in pins.items():need(hashlib.sha256((root/path).read_bytes()).hexdigest()==h,'pin '+path)
def read(p):return (root/p).read_text()
fresh=read('research/current2011-spheres-fresh-base/FreshCarrierSpheres.lean');gen=read('research/current2011-ordinary71-60-generic/OrdinarySphere7160Generic.lean');literal=read('research/current2011-ordinary71-60-literal/OrdinarySphere7160Literal.lean')
def definition(text,name):
 block=text.split('def '+name+' ',1)[1]
 for boundary in ('\ndef ', '\ntheorem ', '\nend ', '\n\n'):
  block=block.split(boundary,1)[0]
 return ' '.join(block.replace('Carrier65.Core','Core').split())
# Literal and generic value have same structure, while their auxiliaries
# must agree definitionally; isolate exactly the source definition blocks.
need(definition(literal,'auxiliary')==definition(fresh,'auxiliary'),'auxiliary definitions')
need(definition(literal,'value71')==definition(gen,'value71'),'value definitions')
for token in ['theorem first_ne_zero','theorem auxiliary_ne_zero','theorem square_ge_one','theorem square_aux_ne_neg_one','theorem sq_one','theorem c_pos']:
 need(token in fresh,'missing interface '+token)
model=read('Lean/DiophantineConsistency/ModelDifferenceRing.lean')
need('theorem nonneg_iff {x : DiffRing V} : 0 ≤ x ↔ ∃ a, x = ι a' in model,'positive representation orientation')
gap=read('research/current2011-shear-positive-gap-representation-draft/PositiveGapRepresentation.lean.src')
need('ι (n+1) = yParent-signedV' in gap and 'tsub_add_cancel_of_le ha1' in gap,'successor orientation')
# A square-coefficient auxiliary norm is never -1 modulo four.
for I in range(4):
 for V in range(4):
  for y in range(4):need((I*I*(V*V-y*y)+y*y)%4!=3,'mod4 exclusion')
# Sphere equation plus nonzero P and U forces both squares to one and H=0.
solutions=0
for P in range(-3,4):
 for U in range(-3,4):
  for QW in range(-3,4):
   for H in range(-3,4):
    if P!=0 and U!=0 and P*P+U*U+(QW-1)**2+H*H==2:
     need(P*P==U*U==1 and H==0,'unit extraction');solutions+=1
need(solutions>0,'vacuous')
for yp in range(-10,11):
 for vs in range(-10,11):
  if vs<yp:
   a=yp-vs;n=a-1;need(n>=0 and n+1==a,'gap successor')
print(json.dumps({'source_pins_verified':len(pins),'literal_generic_value_definitions_compared':True,'mod4_square_aux_cases':64,'finite_sphere_zero_cases':solutions,'gap_successor_controls':210,'scope':'source/finite controls only; no Lean or graph bridge'},sort_keys=True,indent=2))
