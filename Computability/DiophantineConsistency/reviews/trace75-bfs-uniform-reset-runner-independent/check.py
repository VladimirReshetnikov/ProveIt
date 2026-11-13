from pathlib import Path
from hashlib import sha256
from collections import deque
import json,os,sys,tempfile,subprocess
h=Path('research/trace75-bfs-uniform-reset-prototype');run=h/'run.py';out=h/'run-outer.py'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 assert p.is_file(),p
 return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
def hashes(r):return {s:None if v is None else v['sha256'] for s,v in r.items()}
assert sha(run)=='a0fcdb3355c1a9c46205c7db2691268aa95734aaff490e96c231ce111dac8c88' and sha(out)=='1e718c5b9953590aa5a5053496caafb48c2de28e8a2cda8cdd0d17b87fb33a3e'
p=h/'observations/preflight-attempt01';r=json.loads((p/'terminal.json').read_text());assert r['exit']==0 and r['runner_sha256_before']==r['runner_sha256_after']==sha(run) and sha(p/'stdout')==r['stdout_sha256'] and sha(p/'stderr')==r['stderr_sha256'] and not (p/'stderr').read_text();v=json.loads((p/'stdout').read_text());assert v['status']=='PREFLIGHT_PASS' and v['union']==1977 and v['outside']==80 and v['subtrees']=={'DiophantineConsistency.WholeBlockTemporal':281}
pol=h/'observations/policy-attempt01/result.json';r=json.loads(pol.read_text());assert r['status']=='PASS' and len(r['checks'])==18 and all(r['checks'].values()) and r['runner_sha256']==sha(run) and r['test_sha256']==sha(h/'test-policy.py')
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
for root,count in [('DiophantineConsistency.WholeBlockTemporal',281)]:
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
print('PASS: exact preflight, 18 controls, 1977 union + 80 outside current targets/companions, complete BFS support provider subtree and copied-actual-wrapper runner-pin rejection; no Lean launch.')

# Run real v2 helper against same-byte source/object symlink substitution independently.
import ast
code=ast.parse(run.read_text());names={'need','sha','check_root','check_clients'};nodes=[n for n in code.body if isinstance(n,ast.FunctionDef) and n.name in names];ns={'Path':Path,'os':os,'sha256':sha256,'SUFFIXES':('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash','.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')};exec(compile(ast.Module(body=nodes,type_ignores=[]),str(run),'exec'),ns)
with tempfile.TemporaryDirectory(prefix='support-v2-regular-review-') as td:
 d=Path(td);client=d/'client';client.mkdir();(client/'Example.lean').write_bytes(b'source');(client/'Example.olean').write_bytes(b'object');a=sha(client/'Example.lean');b=sha(client/'Example.olean');ns['check_clients']([(client,'Example',a,b)])
 for ext,data in [('.lean',b'source'),('.olean',b'object')]:
  p=client/('Example'+ext);p.unlink();target=d/('target'+ext);target.write_bytes(data);p.symlink_to(target)
  try:ns['check_clients']([(client,'Example',a,b)]);raise AssertionError('same-byte symlink accepted')
  except RuntimeError:pass
  p.unlink();p.write_bytes(data)
print('PASS: actual v2 check_clients rejected independent same-byte source and object symlink mutations.')
for d,n,src,obj in [('/tmp/trace75-bfs-carry-fcp4lu0b','Trace75BFSCarry','84b55b0b1e206c5a9e7d16292581651bbe69cbed51b4f50f8a2faf6563bf1499','d4dc1034131198fd5965e9a23585f81c1182c39ba8b217fb550036acb7b9545e'),('/tmp/trace75-fresh-fixedslots-oyfhiba0','Trace75FixedSlots','e33b9f4ef0132bc2fc0f1adabad939d892b22a446ec1679934f3c34d0902b7d6','63c29a06e1efa989917b77548c8362622a038fe0531373a7f86993343f80cda1')]:
 ns['check_clients']([(Path(d),n,src,obj)])
print('PASS: both accepted provider root paths and four regular source/object files currently match recorded hashes.')

ns['check_clients']([(Path('/tmp/trace75-bfs-support-30d128xr'),'Trace75BFSSupport','06187545b591ad3f6e19bd8f5f9101c6c291bed639e1e10b629584960604ee6b','0795d51ca82af5844510d53a0690ef3940d023f0c78450c38026a8386a255121')])
print('PASS: third support provider root and both regular source/object files match.')

ns['check_clients']([(Path('/tmp/trace75-bfs-cleancarry-t_64ksab'),'Trace75BFSCleanCarry','83673606ed323d304cb97b95f4ad25f120dec09a286f020242d3ce226c6156e8','95408ca90bbf60fd8162eb69dc98f651aae45ca9450492b534aa978c0b0d0c2d')])
print('PASS: fourth clean-carry provider root and both regular source/object files match.')

ns['check_clients']([(Path('/tmp/trace75-bfs-simpleparity-klgreprj'),'Trace75BFSSimpleParity','01e84c924544a56a7ab69db7136cbbb3b5de5158660921b9879ee436253df9ec','c6067db34633e8bb3bd9e0efbd11c61effabd3564346f0877430b51a21944b67'),(Path('/tmp/trace75-bfs-occupied-9u380_i0'),'Trace75BFSOccupied','a82d245ff3c009d1afbb8807c10bfbd1e30167d930d34313238edf8079da47a3','ea99101894f3575e4846087cc0b798843c6ecea62ca1164bd320c2ebd7c23ad8')])
print('PASS: fifth parity and sixth occupied regular provider roots match.')

ns['check_clients']([(Path('/tmp/trace75-bfs-alignedshift-64rdplmm'),'Trace75BFSAlignedShift','c98252d1ecb692a8346539c1a043228535e43fd120f0409175a157628ff83453','e031954c734ca8bbecf74a134acb9bfe2bdeeccebe2550f1a79e85dda76deb64')])
print('PASS: seventh aligned-shift regular provider root matches.')

ns['check_clients']([(Path('/tmp/trace75-bfs-cellshift-9_fgrs9i'),'Trace75BFSCellShift','b71baea359fe136c823fed0d7b462a159f5245a7eb5e2e242766edca64af5f83','757b5a9f37ede9d67c75b97714f68d2c5c2c48c48cdd8845145ccadb82e047b8')])
print('PASS: eighth cell-shift regular provider root matches.')
