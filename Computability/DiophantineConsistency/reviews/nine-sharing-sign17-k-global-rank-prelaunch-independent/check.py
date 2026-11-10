#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-global-rank-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='4d31df1375651e0a8da7caf13954b64804e73b5348ab488bdaf476e84dc984a5' and sha(p/'source-manifest.json')=='51df379c79399f6bd1b16696d4ab3b15551d8e16657ed641748ab6f102356172'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==4
prior=json.loads((root/'research/nine-sharing-sign17-k-adjacent-rank-check/attempt01/state.json').read_text());assert [e['source_sha256'] for e in rows[:3]]==[r['source_sha256'] for r in prior['rows'][15:18]]
for e in rows:
 n=e['module'].split('.')[-1];src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
assert rows[-1]['imports']==['DiophantineConsistency.Sign17KWeightUnion942','DiophantineConsistency.Sign17KAdjacentRank'];s=(p/'src/DiophantineConsistency/Sign17KGlobalRankConditional.lean').read_text()
for t in ('theorem actual_adjacent_of_numeric','hadj : ∀ i : Fin 940','weights i.succ.succ <','weights i.castSucc.succ','rw [Sign17KWeightUnion942.all_weights, Sign17KWeightUnion942.all_weights]','theorem candidate_positions_if','hzero : Sign17KWeightUnion942.indices 0 = 0','hnonzero : ∀ i, i ≠ 0 → Sign17KWeightUnion942.indices i ≠ 0','physicalMap (Sign17KWeightUnion942.indices i) = i','Sign17KAdjacentRank.candidate_positions','actual_adjacent_of_numeric hadj'):assert t in s
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-adjacent-rank-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':4,'scope':'physical ranks conditional on global Start, nonzero, numeric adjacency; no unconditional rank/K/file'},indent=2))
