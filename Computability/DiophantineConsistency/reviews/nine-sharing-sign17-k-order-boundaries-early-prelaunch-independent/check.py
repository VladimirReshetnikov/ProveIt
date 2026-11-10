#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-order-boundaries-early-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='196aca5e06bea409be381fc449c79117003459a3124439d9e2ab43ba275b20bc' and sha(p/'source-manifest.json')=='15dfd5a905dcc49f8bf09f7460beeb5e83bc35baf05d19fa681b704980121ee4'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];prior=json.loads((root/'research/nine-sharing-sign17-k-weight-union224-check/source-manifest.json').read_text())['rows'];assert len(rows)==23 and rows[:22]==prior
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
s=(p/'src/DiophantineConsistency/Sign17KOrderBoundariesEarly.lean').read_text()
for a,b,i in [('Sign17KWeightAggregateProbe','Sign17KWeightAggregateBatch01',31),('Sign17KWeightAggregateBatch01','Sign17KWeightAggregateBatch02',63)]:
 assert f'{b}.weights 0 <\n    {a}.weights {i}' in s
 assert f'selectorWeight (tile ({b}.indices 0)) <\n      selectorWeight (tile ({a}.indices {i}))' in s
 assert f'rw [{b}.all_weights, {a}.all_weights]' in s
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'];assert all(w[i]['weight']>w[i+1]['weight'] for i in (31,95))
c=root/'reviews/nine-sharing-sign17-k-weight-union224-terminal-independent/check.py';assert sha(c)=='75d8927da63b7cb0ae54dcdcd726c3b32655c739ff2661868a4c8c3b44f5b055';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':23,'scope':'numeric and actual-weight boundaries 31/32 and 95/96; no global rank, K or file theorem'},indent=2))
