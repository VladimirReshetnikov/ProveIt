#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];repo=root.parents[1];p=root/'research/nine-sharing-sign17-k-ranked-rawword-retry-check';sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert sha(p/'run.py')=='b43b9ae175f9056316616e6f8c78790a6a9a183b8c79fb2e0e7e65788ae49ba3' and sha(p/'source-manifest.json')=='f02853edc208faf626f6934722df7bbc86a487a3db76006fba486b47b95d4890'
e,=json.loads((p/'source-manifest.json').read_text())['rows'];q=p/'src/DiophantineConsistency/Sign17KRankedRawWord.lean';s=q.read_text();assert e['module']=='DiophantineConsistency.Sign17KRankedRawWord' and e['imports']==['DiophantineConsistency.Sign17KRankedTileSum'] and sha(q)==sha(repo/e['source'])==e['source_sha256'] and re.findall(r'^import ([A-Za-z0-9_.]+)$',s,re.M)==e['imports'] and not re.search(r'(?m)^\s*(axiom|opaque|partial)\b|\b(sorry|admit|native_decide)\b',s)
old=(root/'research/nine-sharing-sign17-k-ranked-rawword-check/src/DiophantineConsistency/Sign17KRankedRawWord.lean').read_text()
delta="  have h0 : (![18, 1004, 2020] : Fin 3 → ℕ) 0 = 18 := rfl\n  have h1 : (![18, 1004, 2020] : Fin 3 → ℕ) 1 = 1004 := rfl\n  have h2 : (![18, 1004, 2020] : Fin 3 → ℕ) 2 = 2020 := rfl\n  simp only [h0, h1, h2]\n"
assert old.replace('  ring\n',delta+'  ring\n')==s
subprocess.run([sys.executable,'-I','-S','-B',str(root/'reviews/nine-sharing-sign17-k-ranked-rawword-terminal-independent/check.py')],capture_output=True,check=True,timeout=180)
for size,weight,pos in [(8,10,978),(9,18,960),(8,27,969),(9,35,942)]:assert f'∑ j : Fin {size}, 2 * 2 ^ ({weight} + j.val) * r ^ (1005 - ({pos} + j.val))' in s
for t in ('rawWord r = r ^ 18 + r ^ 1004 + r ^ 2020','∑ i : Fin 942, 2 * Sign17KWeightUnion942.weights i * r ^ (1005 - i.val)','controls r','unfold rawWord controls','rw [Sign17KRankedTileSum.ranked_tile_sum]','theorem K_ranked : K =','exact rawWord_ranked radix'):assert t in s
c=root/'reviews/nine-sharing-sign17-k-ranked-tile-sum-retry-terminal-independent/check.py';subprocess.run([sys.executable,'-I','-S','-B',str(c)],capture_output=True,check=True,timeout=180)
r=(p/'run.py').read_text();assert "need('Init' in deps" in r and "env['LEAN_NUM_THREADS']='1'" in r and "str(candidates[0])==rec['path']" in r and "rec['realpath']==provider_init['realpath'] and rec['sha256']==provider_init['sha256']" in r and "'-M3600'" in r and 'rss_limit=4*1024**3,mem_floor=10*1024**3,seconds=120,interval=.1' in r
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,timeout=180);assert x.returncode==0 and not x.stderr and json.loads(x.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','controls':[8,9,8,9],'scope':'proposed rawWord/K split into sentinel, ranked tile and control sums; no coefficient/file binding'},indent=2))
