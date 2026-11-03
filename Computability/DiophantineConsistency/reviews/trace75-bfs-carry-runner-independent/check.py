from pathlib import Path
from hashlib import sha256
from collections import deque
import json,os,sys,tempfile,subprocess
h=Path('research/trace75-bfs-carry-prototype');run=h/'run.py';out=h/'run-outer.py'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 assert p.is_file(),p
 return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def hashes(r):return {s:None if v is None else v['sha256'] for s,v in r.items()}
assert sha(run)=='b5f0efe4dd1f853e54a5822e77b585269910b0554511ad94c4aba170f5a7fff0' and sha(out)=='a4368d56f8ede996441664f04d925dbb3d2d19c55c4b9435bc3d5b9052f741f4'
p=h/'observations/preflight-attempt01';r=json.loads((p/'terminal.json').read_text());assert r['exit']==0 and r['runner_sha256_before']==r['runner_sha256_after']==sha(run) and sha(p/'stdout')==r['stdout_sha256'] and sha(p/'stderr')==r['stderr_sha256'] and not (p/'stderr').read_text();v=json.loads((p/'stdout').read_text());assert v['status']=='PREFLIGHT_PASS' and v['union']==1977 and v['outside']==80 and v['subtrees']=={'DirectBFSBandCarry':46,'DiophantineConsistency.ActualTemporalBand':9}
pol=h/'observations/policy-attempt01/result.json';r=json.loads(pol.read_text());assert r['status']=='PASS' and len(r['checks'])==13 and all(r['checks'].values()) and r['runner_sha256']==sha(run) and r['test_sha256']==sha(h/'test-policy.py')
att=Path('research/trace75-fresh-provider-rebuild/observations/attempt01');result=json.loads((att/'result.json').read_text());init=json.loads((att/'initial-union.json').read_text());old=json.loads(Path('research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json').read_text());outside=json.loads(Path('research/direct-bfs-80-coherent-rebuild/observations/attempt01/outside-baseline.json').read_text());expected=dict(init)
for stage in result['stages']:assert stage['status']=='PASS' and stage['exit']==0 and stage['module'] not in expected;expected[stage['module']]=stage['object']
assert len(expected)==1977 and len(outside)==80
lib=Path(result['output_root'])/'lib';pack=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');core=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
for n,b in expected.items():
 for s,x in b.items():
  now=rec(str(lib/n.replace('.','/'))+s);assert (None if now is None else now['sha256'])==(None if x is None else x['sha256']) and (x is None or now['resolved']==x['resolved']),(n,s)
for n,b in outside.items():
 path=None
 for r in [lib,pack,core]:
  x=r/(n.replace('.','/')+'.olean')
  if os.path.lexists(x):assert x.is_file();path=x;break
 assert path and str(path)==b['.olean']['path'],n
 for s,x in b.items():
  now=rec(str(path)[:-6]+s);assert (None if now is None else now['sha256'])==(None if x is None else x['sha256']) and (x is None or now['resolved']==x['resolved']),(n,s)
prior=old['closure']['project'];ext=old['closure']['outside']
for root,count in [('DirectBFSBandCarry',46),('DiophantineConsistency.ActualTemporalBand',9)]:
 seen=set();boundary=set();q=deque([root])
 while q:
  n=q.popleft()
  if n in seen or n in boundary:continue
  if n not in prior:boundary.add(n);continue
  seen.add(n);q.extend(prior[n]['imports'])
 assert len(seen)==count and boundary<=ext.keys()
 for n in seen:assert n in expected and hashes(expected[n])==hashes(prior[n]['companions']),n
 for n in boundary:assert n in outside and hashes(outside[n])==hashes(ext[n]['companions']),n
 print(root,'project',len(seen),'outside',len(boundary))
with tempfile.TemporaryDirectory(prefix='trace75-carry-outer-check-') as td:
 d=Path(td);(d/'run-outer.py').write_bytes(out.read_bytes());(d/'run.py').write_text('raise RuntimeError("NO CHILD")\n');p=subprocess.run([sys.executable,'-I','-S','-B',str(d/'run-outer.py'),'--attempt','attempt99'],capture_output=True,text=True);assert p.returncode and 'input drift' in p.stderr and not (d/'observations').exists()
print('PASS: exact preflight, 13 controls, 1977 union + 80 outside current targets/companions, both complete BFS provider subtrees and copied-actual-wrapper runner-pin rejection; no Lean launch.')
