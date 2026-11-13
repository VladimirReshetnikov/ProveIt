#!/usr/bin/env python3
"""Independent bounded graph and order review; no Lean execution."""
import hashlib, json, random, resource, sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
root=Path(__file__).resolve().parents[2]
pins={
'research/current2011-shear-v-not-one-order-draft/README.md':'d9e2a68533e0163dc7f74b54c7d7aa97389cf38502321f80d9db88affed28324',
'research/current2011-shear-v-not-one-order-draft/ShearOrder.lean.src':'cf261c518f55d885246c3cad418a5da7981d4ea54f9548ebece200df3a39ed99',
'research/current2011-shear-v-not-one-order-draft/check.py':'4a6ad81039005ed91be51db7e10d9f0abdd9b52c92a04b87a5d985b9136b7f1a',
'research/current2011-shear-v-not-one-order-draft/result.json':'97dd54c9f956935c90ffc67f1e27d64e2bc09ae27d190daf41dd2ebb4b596050',
'research/current2011-sheared72-46-candidate/polynomial.json':'cfb30017781968c87e1fa7cba5d08a69b555a7c058ddb1e36b313c74b519e78f',
'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',
'Lean/DiophantineConsistency/Carrier65.lean':'be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154',
'Lean/DiophantineConsistency/ArithmeticCarrier94Indices.lean':'afc99ad41536f55e0f467581e4fbdbd5308036f93b6e3e10b1a5d2f1c113de4a',
'Lean/DiophantineConsistency/ArithmeticCarrier94Extraction.lean':'5e7ef8c7983af9a713b30a02616f00f81c3654b75574fecae944fee369c862f6',
'Lean/DiophantineConsistency/ModelCarrierSpheres.lean':'25e3551c1fb014e958b23dbc944a230aa0db728de5e105aa510878b429a26087'}
def need(b,m):
 if not b: raise RuntimeError(m)
for p,h in pins.items():need(hashlib.sha256((root/p).read_bytes()).hexdigest()==h,'pin '+p)
p=json.loads((root/'research/current2011-ordinary71-60-candidate/polynomial.json').read_bytes());c=json.loads((root/'research/current2011-sheared72-46-candidate/polynomial.json').read_bytes())
need(p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals'],'input interface')
pr=p['source'];cr=c['source'];ip=next(i for i,r in enumerate(pr) if r[0]=='V2');ic=next(i for i,r in enumerate(cr) if r[0]=='y_old')
need(ip==ic and pr[:ip]==cr[:ic] and pr[ip+5:]==cr[ic+6:],'exact common prefix/suffix')
need(pr[ip:ip+5]==[['V2','*','V','V'],['y2','*','y','y'],['aux_gap','-','V2','y2'],['aux_term','*','Aaux','aux_gap'],['Na','+','aux_term','y2']],'parent aux')
need(cr[ic:ic+6]==[['y_old','+','V','y'],['y_old2','*','y_old','y_old'],['sum_yV','+','y_old','V'],['shear_prod','*','y','sum_yV'],['shear_aux','*','Aaux','shear_prod'],['Na','-','y_old2','shear_aux']],'child aux')
need(len(pr)==71 and len(cr)==72 and p['output']==c['output'],'graph sizes')
rng=random.Random(781924);mod=1000000007
for _ in range(80):
 values={n:rng.randrange(-50,51) for n in p['witnesses']+p['fixed_numerals']}
 def evaluate(graph,env):
  env=env.copy()
  for name,op,a,b in graph['source']:
   x=env[a] if isinstance(a,str) else a;y=env[b] if isinstance(b,str) else b
   env[name]=({'*':lambda:x*y,'+':lambda:x+y,'-':lambda:x-y}[op]())%mod
  return env
 ch=evaluate(c,values); pv=values.copy();pv['y']=(ch['V']+values['y'])%mod
 pa=evaluate(p,pv)
 need(pa[p['output']]==ch[c['output']] and pa['Na']==ch['Na'],'finite shear identity')
order=0
for cc in range(1,13):
 for ff in range(2,9):
  for tt in range(1,6):
   for rr in range(-8,9):
    if 2*rr<cc:
     d=cc*tt-rr;left=ff*ff*d
     need(2*d>cc and d>0 and left>=4*d and left>2*cc and left>cc+1,'order implication')
     order+=1
print(json.dumps({'pins_verified':len(pins),'parent_rows':len(pr),'child_rows':len(cr),'exact_graph_common_parts_and_auxiliary_edits':True,'deterministic_signed_shear_controls':80,'order_controls':order,'scope':'finite controls plus separately reviewed ordered-ring argument; no Lean/model binding checked'},sort_keys=True,indent=2))
