#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-rows-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();external=root/'research/nine-sharing-sign14-prefix-formula'
assert sha(p/'run.py')=='958ede9bfdd7d77c2474cfdf2ddc8e08cbd654fa9a7bc26c0649a2242caf0201' and sha(p/'source-manifest.json')=='7c884701d4f351b863aa3ccca4014ac679d937de64aa950bb15c525cf8d1dd83'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];fm=json.loads((external/'manifest.json').read_text());assert len(rows)==4
for e,i in zip(rows,[0,1,3,4]):
 n=f'Sign14PrefixRow{i:02}';src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();q=p/f'src/DiophantineConsistency/row{i:02}.prefix';f=external/f'row{i:02}.prefix';info=fm['rows'][i];assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and e['module']=='DiophantineConsistency.'+n and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports']==['DiophantineConsistency.Sign14PrefixParser'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 assert f'decode p 24 (include_str "row{i:02}.prefix").toList =' in s and f'some (SharingSeed14Degree124.row{i:02} p, [])' in s and '  rfl' in s and info['depth']<24 and sha(q)==sha(f)==info['sha256'] and len(q.read_bytes())==info['length']
c=root/'reviews/nine-sharing-sign14-prefix-probe-terminal-independent/check.py';assert sha(c)=='2e9797b3f4a007068eacdb880a6d5d20a05d7760a43c7520a7ef5b31c9176206';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=120)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r and 'final prefix drift' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':4,'scope':'four remaining embedded prefix row decode proposals; JSON/PDF external binding separate'},indent=2))
