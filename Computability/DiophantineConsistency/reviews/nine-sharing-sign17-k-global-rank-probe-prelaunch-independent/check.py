#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-global-rank-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='8b53194941037c264738b948c6925b652eafc23fbf493b779a4117bcdbd6c3ff' and sha(p/'source-manifest.json')=='be11c383dccc8b922ab5d28479d9e6cddcdde9501f7dbd2c4753b182e75118c4'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign17KGlobalRankProbe.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17KGlobalRankProbe' and e['imports']==['DiophantineConsistency.Sign17KWeightUnion942'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('indices 0 = 0','first_nonzero (i : Fin 16)','indices (i.castAdd 925).succ ≠ 0','first_adjacent (i : Fin 16)','weights (i.castAdd 924).succ.succ <','weights (i.castAdd 924).castSucc.succ'):assert t in s
assert 16+925+1==942 and 16+924+2==942
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'];assert w[0]['index']==0 and all(x['index']!=0 for x in w[1:17]) and all(w[i]['weight']>w[i+1]['weight'] for i in range(1,17))
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-ranking-witness-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'Start, first 16 candidate nonzero/adjacent numeric cases on Fin942; not global rank/K/file'},indent=2))
