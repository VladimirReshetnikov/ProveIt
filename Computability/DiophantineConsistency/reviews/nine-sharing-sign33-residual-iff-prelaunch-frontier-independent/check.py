#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-iff-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'f3021110b970039ba214c63e3558e6b5b0247b2776e79ef1e26ce2a44090c954','provider_survey.py':'67ce5ec2aacc92958fad4c39f08bdce4396526504539dcecf300011c5b929c5e','source-manifest.json':'5dbd9c973ee3304a998be0a8cfd78b24d16c8d0682e850867cabbfbaa2ab1ad9','src/DiophantineConsistency/Sign33ResidualIff.lean':'0a18244fdc58e0859cac5b9f1a8d3a74db3582af897942b6a8da8de6d16c3456'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Sign33ResidualIff.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='0a18244fdc58e0859cac5b9f1a8d3a74db3582af897942b6a8da8de6d16c3456';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Sign33ResidualAssembly','DiophantineConsistency.Sign33ResidualConverse'];assert re.findall(r'^theorem (\w+)',s,re.M)==['seed_zero_iff_all_cuts']
assert 'InternalZero (SharingSeed33.seed p) v ↔ Sign33ResidualAssembly.AllCuts ports v' in s
for n in ('Sign33ResidualAssembly.all_cuts_of_seed_zero','Sign33ResidualConverse.seed_zero_of_all_cuts'):assert n+' p ports v hp0 hp1 hp2 hp3' in s
z=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(z.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled same-valuation seed/AllCuts iff with four casts; no Lean replay'},sort_keys=True,indent=2))
