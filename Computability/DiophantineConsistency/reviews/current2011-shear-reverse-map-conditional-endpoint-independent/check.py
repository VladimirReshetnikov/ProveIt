#!/usr/bin/env python3
"""Independent reverse-graph and conditional endpoint source audit; no Lean."""
import hashlib,json,random,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear-reverse-coordinate-map-draft/README.md':'5309d4c8505de14a2bd8e270a2f31c7ce2811a8b546b5e2d4b392145f09e0f3d',
'research/current2011-shear-reverse-coordinate-map-draft/ReverseCoordinateMap.lean.src':'0b785082d608ff55397d1624f777a4775a6555702dae6ab504fb3c58a2cb84e3',
'research/current2011-shear-reverse-coordinate-map-draft/check.py':'fefc7b926d434578f9bfbf4de5c06f27cf652f156f49091fced73649befb66e1',
'research/current2011-shear-reverse-coordinate-map-draft/result.json':'23c1d0f1e9e5c381db49deda4e978c3af6652a1f9bd3f192020f93af52508d14',
'research/current2011-shear72-conditional-ipra-endpoint-draft/README.md':'641570dfc2c1352cb5fb67392b7916e46d7f97fc8c05ce86f2b513da42a35cd2',
'research/current2011-shear72-conditional-ipra-endpoint-draft/Shear72ConditionalIPRA.lean.src':'4345be11f816398c435b92cf647ea2345014bc84d3868b82512cb0a43e953287',
'research/current2011-shear72-conditional-ipra-endpoint-draft/check.py':'bcb47a97116b5224b77de383e6e497380b914219e1b57f9e35f7cf5b302f5bfc',
'research/current2011-shear72-conditional-ipra-endpoint-draft/pins.json':'ad2605569c64dee0858815ec036b9689ba53daedb778355190904ec3c33ebe7a',
'research/current2011-shear72-conditional-ipra-endpoint-draft/receipt.json':'adeee5f37b310673bc9991b47a50b0645a4a9f839c11e195ed734c50aa397b11',
'research/current2011-shear72-reverse-graph-bounds-draft/Shear72ReverseGraphBounds.lean.src':'51ee53129e01054cc78c83c5f74022dce8fd67d11d34971e5093f4199a845159',
'research/current2011-sheared72-literal-evaluator-draft/Shear72Literal.lean.src':'5f06d64754d71f75b7fef0a9a046c1de9656c9f94e1f36f968c3b81a915a8739',
'research/current2011-ordinary71-60-ipra/OrdinarySphere7160IPRA.lean':'a169a2e71e6699ef84f6196f43ef3bb54245208213cc32f776adadfa622f4421',
'Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean':'d8f79bdea8b0f89235cfd3e19d3977b79fb6012bd0178c06ddbd104e1bb14f06',
'Lean/DiophantineConsistency/IPRAExpressionNative.lean':'f2ecaf302d2e41f7d85a4c5c078f7c9a47f69b8ae4ee40d9b320b4817636b8e8',
'Lean/DiophantineConsistency/IPRAStandardTheory.lean':'c2800acbf0077a1c4d95707a6118e89d6d5cf6a3f9193139d5b2098411b4f120',
'Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean':'11105cf224931655e8fe2b68b0d529363a4fb36bbc902c491a93bb3ca203012c',
'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',
'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f'}
def need(b,m):
 if not b:raise RuntimeError(m)
for path,h in pins.items():need(hashlib.sha256((root/path).read_bytes()).hexdigest()==h,'pin '+path)
def read(p):return (root/p).read_text()
p=json.loads(read('research/current2011-ordinary71-60-candidate/polynomial.json'));c=json.loads(read('research/current2011-sheared72-46-candidate/polynomial.json'))
need(p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals'] and p['witnesses'][12]=='y','coordinate interface')
need([row for row in p['source'] if 'y' in row[2:]]==[['y2','*','y','y']],'parent y-only square')
s=read('research/current2011-shear-reverse-coordinate-map-draft/ReverseCoordinateMap.lean.src')
for x in ['Function.update v 12 (m-1)','tsub_add_cancel_of_le hm1','(ι m : DiffRing V)^2','parent_eval_update_same_square p u _ _ hs','candidate_zero_positive_ordinate CurrentWindowCarry2011.ports u hb hu heval']:
 need(x in s,'reverse interface '+x)
e=read('research/current2011-shear72-conditional-ipra-endpoint-draft/Shear72ConditionalIPRA.lean.src')
for x in ['SameNoZero child parent','forward V v hv','reverse V v hv','bridge child parent (same_no_zero forward reverse)','OrdinarySphere7160IPRA.bridge71','(IPRAStandardTheory.provable_iff _).2','Entailment.C_trans (Entailment.K_left h) (Entailment.K_right z)','Entailment.C_trans (Entailment.K_left z) (Entailment.K_right h)']:
 need(x in e,'endpoint '+x)
b=read('Lean/DiophantineConsistency/HAExpressionNoZeroEquiv.lean');need('(h : SameNoZero e f) (hf : PolynomialBridge f) : PolynomialBridge e' in b,'bridge direction')
need('standardTheory ⊢ φ ↔ nativeTheory ⊢ φ' in read('Lean/DiophantineConsistency/IPRAStandardTheory.lean'),'standard direction')
need('(Semiformula.lMap embedding sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation embedding' in read('Lean/DiophantineConsistency/IPRABoundedRhoZFC.lean'),'GG direction')
rng=random.Random(801216);count=neg=0
for _ in range(100):
 ports=[rng.randrange(0,4) for _ in p['fixed_numerals']];v=[rng.randrange(0,3) for _ in p['witnesses']];u=[x+1 for x in v]
 def evaluate(graph,iv):
  env=dict(zip(graph['witnesses'],iv));env.update(zip(graph['fixed_numerals'],ports))
  for n,op,a,b in graph['source']:
   x=env[a] if isinstance(a,str) else a;y=env[b] if isinstance(b,str) else b
   env[n]=x*y if op=='*' else (x+y if op=='+' else x-y)
  return env
 cv=evaluate(c,u);z=cv['V']+u[12]
 if z==0:continue
 m=abs(z);pv=v.copy();pv[12]=m-1;pu=[x+1 for x in pv]
 need(pu[12]==m and all(pu[j]==u[j] for j in range(14) if j!=12),'parent shift')
 pvout=evaluate(p,pu);need(pvout['polynomial']==cv['polynomial'],'same-square entire output')
 count+=1;neg+=z<0
need(count>=50 and neg>0,'controls missing')
# For all possible existence values, both witness maps enforce no-zero iff.
for parent in (False,True):
 for child in (False,True):
  forward=(not parent) or child;reverse=(not child) or parent
  if forward and reverse:need((not child)==(not parent),'no-zero direction')
print(json.dumps({'source_pins_verified':len(pins),'parent_y_only_square':True,'reverse_shift_and_full_graph_controls':count,'negative_signed_ordinates':neg,'conditional_bridge_and_GG_directions_inspected':True,'scope':'source/finite controls only; maps and endpoints remain unelaborated and conditional'},sort_keys=True,indent=2))
