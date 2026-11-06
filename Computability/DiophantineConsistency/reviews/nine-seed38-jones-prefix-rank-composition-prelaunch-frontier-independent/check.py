#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-seed38-jones-prefix-rank-composition-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'6d4e1f704404149fc09d2dc2ee4522013bee9df92ed2ab5e2e3f4ebab062be4a','provider_preflight.py':'39d81c097f8b79d416dcd0896fa8aa03bc92404668d5c564bd2cb96150ab12ab','source-manifest.json':'33c2f62130e0d015ad2cddc484a170dc4ef4bceaf9bb88898e59682dfd09d0bb','src/DiophantineConsistency/Norm38MacroRankComposition.lean':'7456d37335417d1aec5cf8ed97d1d1cb9eaa117d27f5a8a04fb945dbab3771ca'}.items():assert h(p/n)==v
s=(p/'src/DiophantineConsistency/Norm38MacroRankComposition.lean').read_text();rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==1 and rows[0]['source_sha256']=='7456d37335417d1aec5cf8ed97d1d1cb9eaa117d27f5a8a04fb945dbab3771ca';assert rows[0]['imports']==re.findall(r'^import ([\w.]+)$',s,re.M)==['DiophantineConsistency.Norm38MacroRankCodeLink','DiophantineConsistency.Norm38MacroPrefixBPower'];assert re.findall(r'^theorem (\w+)',s,re.M)==['d11_rankCode'] and re.findall(r'^#print axioms (\w+)',s,re.M)==['d11_rankCode']
concl=s.split(':= by',1)[0];assert [int(x) for x in re.findall(r'd10\.values a ⟨(\d+), by decide⟩',concl)]==[0,4,7,5,3,2,8,6]
found=re.findall(r'd10\.values a \(\(Fin\.last (\d+)\)((?:\.castSucc)*)\)',s);assert [(int(i),x.count('.castSucc')) for i,x in found]==[(0,9),(1,8)]
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'uncompiled d11 rankCode composition; no Lean replay'},sort_keys=True,indent=2))
