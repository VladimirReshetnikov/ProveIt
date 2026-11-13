#!/usr/bin/env python3
"""Pin independent source review and check actual graph coordinate dependencies."""
import hashlib,json,random,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear72-reverse-magnitude-draft/README.md':'99387b0afe0246076e38ae444750e7f28a9fe7860ab206072491a0f0d856b9cc',
'research/current2011-shear72-reverse-magnitude-draft/Shear72ReverseMagnitude.lean.src':'70b8b4f932357d6f6a6c5b23f7b98c2bd699a0413b4e99f58e95179b71ce998b',
'research/current2011-shear72-reverse-magnitude-draft/check.py':'769508e6bc04d3375d4f7ed30767a69851ec1d61797abb23831fbc3e680c6f9a',
'research/current2011-shear72-reverse-magnitude-draft/pins.json':'ac33b5747497bc5a7c45dc20e4f481cfb5b09b11e61b8372b283678ab757045f',
'research/current2011-shear72-reverse-magnitude-draft/receipt.json':'0f1f87b7d446735bc9e712582e3a7059245099cd5ad7115b9da510caf22ec71c',
'research/current2011-shear72-reverse-generic-model-draft/README.md':'d30af707355f04c7d1364a03be3ae11e24673e1468f1ba38b98883e782b1bb77',
'research/current2011-shear72-reverse-generic-model-draft/Shear72ReverseGenericModel.lean.src':'d8cef08cb2fd65553063c58aaf2a3867a8681752639d8d87d91ea822e626e019',
'research/current2011-shear72-reverse-generic-model-draft/check.py':'e5be63b6cbd3c2dfcf0ded6069996451922dde55e13b014c206fcbdbf724b8ca',
'research/current2011-shear72-reverse-generic-model-draft/pins.json':'a78a8ddc232197213211313031ee6e19a4c2f64095873928f3814d94aa5edc37',
'research/current2011-shear72-reverse-generic-model-draft/receipt.json':'23cf39118a8677641a99006edf1e1755bf9196a460fff0d4bc90564be1809ac3',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
'Lean/DiophantineConsistency/ZRows/CoprimeSquares.lean':'263e2de4a7ab0d1006255115f280e6260158f6bff0289a5da06921e40a850801',
'research/current2011-shear-ordinate-nonzero-order-draft/ShearNonzero.lean.src':'c67931ea31c2fbedc6d0976f5d188fe9bf5633bfe4a51062a0c64e81dd1a66f3',
'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f',
'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27'}
def need(b,m):
 if not b:raise RuntimeError(m)
for p,d in pins.items():need(hashlib.sha256((root/p).read_bytes()).hexdigest()==d,'pin '+p)
p=json.loads((root/'research/current2011-ordinary71-60-candidate/polynomial.json').read_bytes());c=json.loads((root/'research/current2011-sheared72-46-candidate/polynomial.json').read_bytes())
need(p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals'],'coordinates')
need([x for x in p['source'] if 'y' in x[2:]]==[['y2','*','y','y']],'parent y must only occur in square')
need([x for x in c['source'] if 'y' in x[2:]]==[['y_old','+','V','y'],['shear_prod','*','y','sum_yV']],'child y dependency')
need('theorem abs_eq_ι (A : DiffRing V) : ∃ a : V, |A| = ι a' in (root/'Lean/DiophantineConsistency/ZRows/CoprimeSquares.lean').read_text(),'magnitude orientation')
need('theorem ι_le_ι {a b : V} : ι a ≤ ι b ↔ a ≤ b' in (root/'Lean/DiophantineConsistency/ModelDifferenceRing.lean').read_text(),'embedding order')
need('theorem ordinate_ne_zero (A I V y rest : R)' in (root/'research/current2011-shear-ordinate-nonzero-order-draft/ShearNonzero.lean.src').read_text(),'generic source')
rng=random.Random(139821);checked=0
for _ in range(80):
 v={x:rng.randrange(-4,5) for x in p['witnesses']+p['fixed_numerals']}
 def evalgraph(g,values):
  e=values.copy()
  for out,op,a,b in g['source']:
   x=e[a] if isinstance(a,str) else a;y=e[b] if isinstance(b,str) else b
   e[out]=x*y if op=='*' else (x+y if op=='+' else x-y)
  return e
 a=evalgraph(c,v);z=a['V']+v['y']
 if z==0:continue
 v2=v.copy();v2['y']=abs(z);b=evalgraph(p,v2)
 need(b[p['output']]==a[c['output']] and b['Na']==a['Na'],'magnitude output');checked+=1
need(checked>=50,'too few controls')
print(json.dumps({'source_pins_verified':len(pins),'parent_y_only_through_square':True,'source_magnitude_and_order_interfaces_checked':True,'nonzero_signed_graph_controls':checked,'scope':'bounded controls and source review; prospective imports and model maps unelaborated'},sort_keys=True,indent=2))
