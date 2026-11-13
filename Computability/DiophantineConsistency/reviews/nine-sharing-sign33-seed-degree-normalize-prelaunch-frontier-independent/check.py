#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-seed-degree-normalize-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(p/'run.py')=='c68c3cbf584ac93ba99173b02acaf714ca4551b16e59e68b48b6e077d9b93118'
assert h(p/'source-manifest.json')=='b5f00d20f6e747f5c68509403a5a540c8c5d427236a9984db5e71525ef502255'
rows=json.loads((p/'source-manifest.json').read_text())['rows']
expected=[('SharingSeed33Normalize','e89f09758397adb06ac2680706665c57b21c2f19f428eb413c62373753d6c011','SharingSeed33Syntax'),('SharingSeed33Weighted','b45926431f101585bef9e2a2d8c48dc51fe8f127f671e1e466057b6df1903a10','SharingSeed33Syntax'),('SharingSeed33Degree','443ce0bb48aaf6c539adf780e2041a36aaab1a6172e46045462387b0a7dd670c','SharingSeed33Weighted')]
assert len(rows)==3
for row,(name,digest,dep) in zip(rows,expected):
 src=p/'src/DiophantineConsistency'/f'{name}.lean';assert h(src)==digest==row['source_sha256'];assert row['module']=='DiophantineConsistency.'+name
 assert row['imports']==['DiophantineConsistency.'+dep]==re.findall(r'^import ([\w.]+)$',src.read_text(),re.M)
sources='\n'.join((p/'src/DiophantineConsistency'/f'{n}.lean').read_text() for n,_,_ in expected)
assert len(re.findall(r'^#print axioms ',sources,re.M))==5
res=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);j=json.loads(res.stdout);assert j['status']=='PASS_NO_LEAN_PREFLIGHT' and j['stage_count']==3
print(json.dumps({'status':'PASS','preflight':j,'scope':'three uncompiled symbolic theorem clients; external JSON check remains external'},indent=2,sort_keys=True))
