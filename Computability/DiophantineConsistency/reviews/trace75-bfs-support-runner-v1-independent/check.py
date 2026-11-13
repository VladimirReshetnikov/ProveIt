from pathlib import Path
from hashlib import sha256
from collections import deque
import json,os,sys,tempfile,subprocess
h=Path('research/trace75-bfs-support-prototype');run=h/'run.py';out=h/'run-outer.py'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 assert p.is_file(),p
 return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def hashes(r):return {s:None if v is None else v['sha256'] for s,v in r.items()}
assert sha(run)=='be0f4a2d7af098d07df7a8cc834e4b2f4c004c0305f5c110a56165ecbb4e9c71' and sha(out)=='4861f8edfdae91d4e19da51ff1c46fa8548a48a42d7835a99ec2a353745d76fd'
p=h/'observations/preflight-attempt01';r=json.loads((p/'terminal.json').read_text());assert r['exit']==0 and r['runner_sha256_before']==r['runner_sha256_after']==sha(run) and sha(p/'stdout')==r['stdout_sha256'] and sha(p/'stderr')==r['stderr_sha256'] and not (p/'stderr').read_text();v=json.loads((p/'stdout').read_text());assert v['status']=='PREFLIGHT_PASS' and v['union']==1977 and v['outside']==80 and v['subtrees']=={'DiophantineConsistency.CleanModelSupport':128}
pol=h/'observations/policy-attempt01/result.json';r=json.loads(pol.read_text());assert r['status']=='PASS' and len(r['checks'])==16 and all(r['checks'].values()) and r['runner_sha256']==sha(run) and r['test_sha256']==sha(h/'test-policy.py')
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
for root,count in [('DiophantineConsistency.CleanModelSupport',128)]:
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
print('PASS: exact preflight, 16 controls, 1977 union + 80 outside current targets/companions, complete BFS support provider subtree and copied-actual-wrapper runner-pin rejection; no Lean launch.')
# Show the v1 provider guard accepts replacing a captured regular object with a same-byte symlink.
import ast
code=ast.parse(run.read_text());names={'need','sha','check_root','check_clients'};nodes=[n for n in code.body if isinstance(n,ast.FunctionDef) and n.name in names];ns={'Path':Path,'os':os,'sha256':sha256,'SUFFIXES':('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(run),'exec'),ns)
with tempfile.TemporaryDirectory(prefix='support-target-drift-review-') as td:
 d=Path(td);client=d/'client';client.mkdir();(client/'Example.lean').write_bytes(b'source');(client/'Example.olean').write_bytes(b'object');a=sha(client/'Example.lean');b=sha(client/'Example.olean');ns['check_clients']([(client,'Example',a,b)]);(client/'Example.olean').unlink();target=d/'other';target.write_bytes(b'object');(client/'Example.olean').symlink_to(target);ns['check_clients']([(client,'Example',a,b)]);assert (client/'Example.olean').is_symlink()
print('HOLD: actual v1 check_clients accepted same-byte replacement of a previously regular provider object by a symlink to a different target.')
