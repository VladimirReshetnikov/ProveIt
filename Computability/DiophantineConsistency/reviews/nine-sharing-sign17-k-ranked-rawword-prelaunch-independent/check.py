#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-ranked-rawword-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='abf498613300b403a9bbc6b264e6152d816f49cd59cdd783f31a8f447d5a9ec8' and sha(p/'source-manifest.json')=='5bc2573c27710660a7405eea6b5b6f5cf7ec0e38fefe111da1ebf64006e7c4c8'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KRankedRawWord.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KRankedRawWord' and e['imports']==['DiophantineConsistency.Sign17KRankedTileSum'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
for size,weight,pos in [(8,10,978),(9,18,960),(8,27,969),(9,35,942)]:assert f'∑ j : Fin {size}, 2 * 2 ^ ({weight} + j.val) * r ^ (1005 - ({pos} + j.val))' in s
for t in ('rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020','∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * r ^ (1005 - i.val)','controls r','unfold rawWord controls','rw [Sign17KRankedTileSum.ranked_tile_sum]','theorem K_ranked : K =','exact rawWord_ranked radix'):assert t in s
c=root/'reviews/nine-sharing-sign17-k-ranked-tile-sum-retry-terminal-independent/check.py';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','controls':[8,9,8,9],'scope':'proposed rawWord/K split into sentinel, ranked tile and control sums; no coefficient/file binding'},indent=2))
