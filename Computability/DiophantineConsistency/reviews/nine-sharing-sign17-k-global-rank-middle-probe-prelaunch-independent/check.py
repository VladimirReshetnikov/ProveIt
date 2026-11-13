#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-global-rank-middle-probe-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='4117697368e3cdde91820f1d2f47c3f070db25546d2aa9bd015cfd8c5603ccd5' and sha(p/'source-manifest.json')=='d6d287e1eb4df3112115fe6cee760ee32c2e16463954369739acf4b877f64c1c'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];src=p/'src/DiophantineConsistency/Sign17KGlobalRankMiddleProbe.lean';s=src.read_text();assert e['module']=='DiophantineConsistency.Sign17KGlobalRankMiddleProbe' and e['imports']==['DiophantineConsistency.Sign17KWeightUnion942'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for t in ('def nonzeroIndex (i : Fin 64) : Fin 941 := (Fin.natAdd 448 i).castAdd 429','def adjacentIndex (i : Fin 64) : Fin 940 := (Fin.natAdd 448 i).castAdd 428','indices (nonzeroIndex i).succ ≠ 0','weights (adjacentIndex i).succ.succ <','weights (adjacentIndex i).castSucc.succ'):assert t in s
assert 448+64+429==941 and 448+64+428==940
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'];assert all(w[i]['index']!=0 for i in range(449,513)) and all(w[i]['weight']>w[i+1]['weight'] for i in range(449,513))
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-ranking-witness-independent','nine-sharing-sign17-k-global-rank-probe-terminal-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'64 middle candidate nonzero/adjacent numeric cases on Fin942; not global rank/K/file'},indent=2))
