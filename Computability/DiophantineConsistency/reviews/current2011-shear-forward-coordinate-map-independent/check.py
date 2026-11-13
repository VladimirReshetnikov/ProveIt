#!/usr/bin/env python3
"""Pin source, graph dependence and finite successor-coordinate diagnostics."""
import hashlib,json,random,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear-forward-coordinate-map-draft/README.md':'2a33910ea0bb3a86e2f810839398efcb764018dfdd06397e28fcaefff2f04b69',
'research/current2011-shear-forward-coordinate-map-draft/ForwardCoordinateMap.lean.src':'05bb78857a208caa5cfec1dfe78ccda68b6aa4f552db62adf271faff5384a9c6',
'research/current2011-shear-forward-coordinate-map-draft/check.py':'0a88a382002ff7342a2ccf22ad90d73e1d1067ba4f1c2ca2d493bbb7a565562e',
'research/current2011-shear-forward-coordinate-map-draft/result.json':'eba78ff9060f7ea73365870139d50f25c1581916c81ed38603ca62e662442d31',
'research/current2011-sheared72-literal-evaluator-draft/Shear72Literal.lean.src':'5f06d64754d71f75b7fef0a9a046c1de9656c9f94e1f36f968c3b81a915a8739',
'research/current2011-shear-positive-gap-representation-draft/PositiveGapRepresentation.lean.src':'330544ffaedd3afc061931ace2b0518f3ebd5b855e56516944cc34322033b049',
'research/current2011-shear-current-port-cast-draft/CurrentPortCast.lean.src':'be27b59b37e99d41eb90f6913ef6f19f0d943581c51ded85477477e9f46fc320',
'research/current2011-shear-forward-norm-order-draft/ForwardNormOrder.lean.src':'de67ebbb8699e8f43f28f8db6caca0da8edaed522503e4ba9a98f4d12b7a5b2d',
'research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src':'fb39f3cb211700acd7e431da2f7a4e95a256a4a6f98087f8db0cb163beb9101a',
'Lean/DiophantineConsistency/Carrier65.lean':'be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998',
'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean':'f1d7f3835bc2a183b0767497a45ffdd0a54e6aab086b259ccce3de4af9392cb6',
'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',
'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f',
'research/normalized106-fresh-base-model-build/FreshModel106.lean':'61e64a2ef559c3da369021df2705cd76f957bc0ea971467b80d627eaa9422769'}
def need(b,m):
 if not b:raise RuntimeError(m)
for path,h in pins.items():need(hashlib.sha256((root/path).read_bytes()).hexdigest()==h,'pin '+path)
p=json.loads((root/'research/current2011-ordinary71-60-candidate/polynomial.json').read_bytes());c=json.loads((root/'research/current2011-sheared72-46-candidate/polynomial.json').read_bytes())
need(p['witnesses'][12]==c['witnesses'][12]=='y','y slot')
rows={r[0]:r for r in p['source']};todo=['V'];visited=set()
while todo:
 n=todo.pop()
 if n in visited:continue
 visited.add(n)
 if n in rows:todo.extend(x for x in rows[n][2:] if isinstance(x,str))
need('y' not in visited,'V depends on y')
core=(root/'Lean/DiophantineConsistency/Carrier65.lean').read_text();need('let V := f ^ 2 * (c * T - rank) - c' in core and 'let y := v 12' in core,'core V/y')
s=(root/'research/current2011-shear-forward-coordinate-map-draft/ForwardCoordinateMap.lean.src').read_text()
for x in ['Function.update u 12 x','Function.update v 12 n','ι (n+1)', 'shifted_child_eq_update','shear_inverse currentP (shiftedRing v) (ι (n+1)) hrep','positive_gap_as_successor','forward_zero_of_rep v n hn hz']:
 need(x in s,'interface '+x)
sem=1000000007;rng=random.Random(204772);done=0
for _ in range(80):
 ports=[rng.randrange(1,4) for _ in p['fixed_numerals']];v=[rng.randrange(0,3) for _ in p['witnesses']]
 def evaluate(graph,iv):
  e=dict(zip(graph['witnesses'],iv));e.update(zip(graph['fixed_numerals'],ports))
  for name,op,a,b in graph['source']:
   x=e[a] if isinstance(a,str) else a;y=e[b] if isinstance(b,str) else b
   # V is required as an integer for the positivity representative.
   e[name]=x*y if op=='*' else (x+y if op=='+' else x-y)
  return e
 u=[x+1 for x in v];V=evaluate(p,u)['V'];u[12]=max(0,V)+2;v[12]=u[12]-1
 n=u[12]-V-1;need(n>=0,'positive difference');child=v.copy();child[12]=n;cu=[x+1 for x in child]
 ce=evaluate(c,cu);need(ce['V']==V,'V update')
 sheared=cu.copy();sheared[12]=V+cu[12];need(sheared==u,'full coordinate inverse')
 pe=evaluate(p,u);need((pe['polynomial']-ce['polynomial'])%sem==0,'polynomial update');done+=1
print(json.dumps({'source_pins_verified':len(pins),'parent_V_dependency_excludes_y':True,'coordinate':12,'successor_update_graph_controls':done,'scope':'source and finite algebra only; no Lean, model cast or endpoint check'},sort_keys=True,indent=2))
