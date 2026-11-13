#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-global-chunks-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='8d9cfc526eab01dd60b2793eeff66a5be73883fe428ddd25563c64e42a32ee3a' and sha(p/'source-manifest.json')=='66ba26985d132078dc1f2fda1688a69838c15ce3dd58a8b2cc2e789b956ce7cc'
rows=json.loads((p/'source-manifest.json').read_text())['rows'];assert len(rows)==15;non=[];adj=[]
for i,e in enumerate(rows):
 n=f'Sign17KGlobalChunk{i:02}';src=p/'src/DiophantineConsistency'/(n+'.lean');s=src.read_text();assert e['module']=='DiophantineConsistency.'+n and e['imports']==['DiophantineConsistency.Sign17KWeightUnion942'] and sha(src)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
 offset=64*i;ns=64 if i<14 else 45;ads=64 if i<14 else 44
 for t in (f'def nonzeroIndex (i : Fin {ns}) : Fin 941 := (Fin.natAdd {offset} i).castAdd {941-offset-ns}',f'def adjacentIndex (i : Fin {ads}) : Fin 940 := (Fin.natAdd {offset} i).castAdd {940-offset-ads}',f'theorem nonzero (i : Fin {ns})',f'theorem adjacent (i : Fin {ads})','indices (nonzeroIndex i).succ ≠ 0','weights (adjacentIndex i).succ.succ <','weights (adjacentIndex i).castSucc.succ'):assert t in s
 assert ('theorem start_index' in s)==(i==0);non.extend(range(offset+1,offset+1+ns));adj.extend(range(offset+1,offset+1+ads))
assert non==list(range(1,942)) and adj==list(range(1,941))
w=json.loads((root/'research/nine-sharing-sign17-k-ranking-witness/witness.json').read_text())['rows'];assert w[0]['index']==0 and all(w[i]['index']!=0 for i in non) and all(w[i]['weight']>w[i+1]['weight'] for i in adj)
for f in ('nine-sharing-sign17-k-weight-union942-terminal-independent','nine-sharing-sign17-k-global-rank-middle-probe-terminal-independent','nine-sharing-sign17-k-ranking-witness-independent'):
 subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews'/f/'check.py')],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','stages':15,'nonzero_cases':len(non),'adjacent_cases':len(adj),'scope':'bounded candidate numeric chunks; global assembly/rank/K/file separate'},indent=2))
