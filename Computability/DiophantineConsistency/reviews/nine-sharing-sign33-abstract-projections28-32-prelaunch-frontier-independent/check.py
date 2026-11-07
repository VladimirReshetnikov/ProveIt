#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-abstract-projections28-32-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for n,h in {'run.py':'5717e8fe1be0f05f38900589f957860da2684d9badb769e9b79a786e37899655','provider_survey.py':'ae82422cb12cd3add5d2b21ee16071ff08197c07873bf0c09016094e4b156f5d','source-manifest.json':'9b3b3eb8f5b41156285acead9ba28bf694258346dce61a986d03391f3386fea4'}.items():assert sha(p/n)==h
rows=json.loads((p/'source-manifest.json').read_text())['rows'];expected=[('Sign33AbstractProjection28','a77ad63eb01a7e4064e5d94caa71300c2eb3c141cec1d0283803424038a637e1',28,27,29),('Sign33AbstractProjection32','577eded9c73da41f1757c540ff46a51f2a0ca9d94b08b586f1081c7c462b8762',32,31,35)];assert len(rows)==2
f=(d/'research/nine-sharing-sign33-abstract-projection22-check/src/DiophantineConsistency/Sign33AbstractTuple.lean').read_text();vec=[x.strip() for x in re.search(r'!\[(.*?)\]',f,re.S).group(1).split(',')]
for row,(n,h,i,j,k) in zip(rows,expected):
 q=p/'src/DiophantineConsistency'/f'{n}.lean';s=q.read_text();assert row['module']=='DiophantineConsistency.'+n and sha(q)==row['source_sha256']==h and re.findall(r'^import ([\w.]+)$',s,re.M)==row['imports']==['DiophantineConsistency.Sign33AbstractTuple'];assert vec[j]==f'w {k}' and f') {i} = w {k}' in s and f'({j} : Fin 33).succ = ({i} : Fin 34)' in s and f'ports u {k} :=' in s and re.findall(r'^theorem (\w+)',s,re.M)==['template','project'] and s.count('#print axioms ')==2
survey=(p/'provider_survey.py').read_text();assert '2464c7f1a7f03d85770c354c5dbb5130c51edf6fdce392e297732373b0cdb8eb' in survey and 'Sign33AbstractTuple' in survey
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=300);o=json.loads(r.stdout);assert not r.stderr and o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==2
print(json.dumps({'status':'PASS','preflight':o,'scope':'abstract/concrete projections 28 and 32; no Lean replay'},indent=2,sort_keys=True))
