#!/usr/bin/env python3
"""Pins and finite controls for the proposed sign-free calibration replay."""
import gzip,hashlib,json,math
from pathlib import Path
D=Path(__file__).resolve().parents[2]
pins={'research/ordinary14-shifted-guard87-probe/candidate.json':'405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210','Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3','Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean':'d02beb02122e682deef3e89c3dcb8e3e6aea31ddfbc4f320fe6af9a3df7f9a6b','Lean/DiophantineConsistency/Compact44/FreeJEarlyIndex.lean':'ab9b8e34903eff1e33e81b6a75438797eef1f2dab84595e23516b44de774ea3d','Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean':'e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816','Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390','Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h
p=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';binding=json.loads((p/'ACTIVE_BINDING.json').read_bytes());assert hashlib.sha256((p/'ACTIVE_BINDING.json').read_bytes()).hexdigest()=='6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'
v={}
for name,meta in binding['ports'].items():
 z=(p/meta['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==meta['sha256_gzip'];raw=gzip.decompress(z);assert hashlib.sha256(raw).hexdigest()==meta['sha256_raw'];v[name]=int.from_bytes(raw,'little')
assert v['beta']>=46 and 0<v['MC']<v['beta'] and 0<v['MF']<2*v['beta'] and v['K0']>=0
count=0
for q in range(3,60):
 for X in range(1,8):
  for y0 in range(1,5):
   Y=q**3*y0;a=Y*(X+1);H=3+4*a
   assert math.gcd(H,q**5)<=3
   assert (q**5//math.gcd(H,q**5))%(q**4)==0
   assert q*q*Y*Y*a>H
   count+=1
# A complete small Pell identity distinguishes the correct i'=i mapping
# from the erroneous extra-Delta choice.
f,L=1,0
for _ in range(9):f,L=2*f+3*L,f+2*L
assert L%9==0
c=3; delta=3; i=delta*L//9
assert (i*c*c)**2+delta==delta*f*f
assert (delta*i*c*c)**2+delta!=delta*f*f
print(json.dumps({'source_files_and_graph_pinned':len(pins),'actual_port_bounds_checked':True,'finite_orientation_and_gcd_controls':count,'scope':'source and finite checks for proposed external replay; no modified-graph Lean client, endpoint replay or PDF binding'},sort_keys=True,indent=2))
