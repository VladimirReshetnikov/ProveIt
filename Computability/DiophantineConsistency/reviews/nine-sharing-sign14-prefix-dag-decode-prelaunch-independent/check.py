#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign14-prefix-dag-decode-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='2c3bbc1e88ba209cfd5960ceb307ad29983ec82329352f7597508382c65e28c0' and sha(p/'source-manifest.json')=='1cca01caea10ee9279691dbd5e5ac41fe068bef80ef6915a344a5f57d99e1de1'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==5;depths=[]
for i,e in enumerate(rows):
 n=f'Sign14PrefixDagDecode{i:02}';q=p/'src/DiophantineConsistency'/(n+'.lean');s=q.read_text();prev='Sign14PrefixDagRow04' if i==0 else f'Sign14PrefixDagDecode{i-1:02}';assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.'+prev] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 for t in (f'theorem row{i:02}_depth : depth Sign14PrefixCode.row{i:02} ≤ 24 := by decide',f'decode p 24 row{i:02}Bytes = some (SharingSeed14Degree124.row{i:02} p, [])',f'rw [row{i:02}Bytes_eq]',f'decode_encode p Sign14PrefixCode.row{i:02} 24 row{i:02}_depth []',f'[List.append_nil, row{i:02}_interpret]'):assert t in s
 st=[]
 for ch in reversed((root/'research/nine-sharing-sign14-prefix-formula'/f'row{i:02}.prefix').read_text()):
  if ch in '+-*':a=st.pop();b=st.pop();st.append(1+max(a,b))
  else:assert ch in 'BKCF1234abcdefghijklmno';st.append(1)
 assert len(st)==1 and st[0]<=24;depths.append(st[0])
for f in ('nine-sharing-sign14-prefix-dag-composition-terminal-independent','nine-sharing-sign14-prefix-dag-fragments-independent','nine-sharing-sign14-prefix-reflection-retry03-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':5,'external_prefix_depths':depths,'scope':'decode five embedded fragment DAG row lists conditional on Lean; original file/JSON/PDF external'},indent=2))
