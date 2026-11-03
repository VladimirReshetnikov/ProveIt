from pathlib import Path
from hashlib import sha256
import json,os
base=Path('research/trace75-bfs-provider-preflight');obs=base/'observations/scan-attempt01';outer=base/'observations/outer-attempt01'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 assert p.is_file(),p
 return {'path':str(p),'resolved':str(p.resolve(strict=True)),'sha256':sha(p),'link':os.readlink(p) if p.is_symlink() else None}
p=obs/'result.json';assert sha(p)=='e27f1cb8694aab43a1023abcce95f7fbc7846d4860dac4b96046391da3dd1e8d';j=json.loads(p.read_text());assert j['status']=='PASS'
t=outer/'terminal.json';assert sha(t)=='5a916a82f6bf12f2102f00d48183229c669aeda6fc760edeb4df670c17b468c7';o=json.loads(t.read_text());assert o['exit']==0 and o['scanner_sha256_before']==o['scanner_sha256_after']==j['runner_sha256']==sha(base/'scan-v2.py')=='c8e55712c29c8fb60de059c6451ffc5a4aa93319c3cfe20c70952837b4e1e2e2';assert sha(base/'scan-outer.py')==o['wrapper_sha256'] and sha(outer/'stdout')==o['stdout_sha256'] and sha(outer/'stderr')==o['stderr_sha256'] and not (outer/'stderr').read_text()
for p,h in j['inputs'].items():assert sha(p)==h
old=json.loads(Path('research/direct-bfs-80-coherent-rebuild/observations/attempt01/result.json').read_text());prior=old['closure']['project'];tr=json.loads(Path('research/trace75-root-probe/observations/fixedcongruence-attempt01/terminal.json').read_text());paths=[Path(p) for p in tr['lean_path'].split(':')];lib=Path('/tmp/direct90-ipra-join-b66u_qqo/lib');paths.insert(0,Path(tr['output_root']));paths.insert(paths.index(lib),Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib'));paths.append(Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean'));assert list(map(str,paths))==j['search_path']==json.loads((obs/'search-path.json').read_text())
proj=j['selected_project'];outside=j['selected_outside'];headers=j['headers'];assert len(proj)==248 and len(outside)==28 and set(headers)==set(proj) and not (set(proj)&set(outside));assert j['reader_env']=={'PATH':'/usr/bin:/bin'}
for n,bundle in list(proj.items())+list(outside.items()):
 rel=Path(*n.split('.')).with_suffix('.olean');selected=None
 for p in paths:
  x=p/rel
  if os.path.lexists(x):assert x.is_file();selected=x;break
 assert selected and str(selected)==bundle['.olean']['path'],n
 stem=str(selected)[:-6]
 for ext,val in bundle.items():assert rec(stem+ext)==val,(n,ext)
for n,h in j['root_hashes'].items():assert proj[n]['.olean']['sha256']==h
assert j['root_hashes']['Trace75FixedCongruence']==tr['object_sha256'] and j['root_hashes']['DirectBFSBandCarry']==prior['DirectBFSBandCarry']['record']['sha256']
reused=set(j['header_reuse']);assert len(reused)==192
for n in reused:assert n in prior and prior[n]['record']['sha256']==proj[n]['.olean']['sha256'] and prior[n]['imports']==headers[n]
parsed={};path_to_name={b['.olean']['path']:n for n,b in proj.items()}
assert len(j['batches'])==11
for i,batch in enumerate(j['batches']):
 so=obs/f'header-{i:03}.stdout';se=obs/f'header-{i:03}.stderr';assert batch['exit']==0 and batch['reason'] is None and batch['env']==j['reader_env'] and sha(so)==batch['stdout_sha256'] and sha(se)==batch['stderr_sha256'] and not se.read_text()
 cur=None
 for line in so.read_text().splitlines():
  if line.startswith('BEGIN '):assert cur is None and line[6:] in path_to_name;cur=path_to_name[line[6:]];assert cur not in parsed;parsed[cur]=[]
  elif line.startswith('IMPORT ') and cur is not None:parsed[cur].append(line[7:])
  elif line=='END' and cur is not None:cur=None
  else:raise AssertionError((i,line))
 assert cur is None
assert set(parsed)==set(proj)-reused and all(headers[n]==v for n,v in parsed.items())
five=['DiophantineConsistency.'+n for n in ['ModelRatioBounds','ArithmeticNegativeNorms','ArithmeticCarrierRadix2011','ArithmeticWindowInterface','ArithmeticCarrierSoundness2011']]
for root,r in j['roots'].items():
 todo=[root];seen=set();out=set()
 while todo:
  n=todo.pop()
  if n in seen or n in out:continue
  if n in headers:seen.add(n);todo.extend(headers[n])
  else:assert n in outside,n;out.add(n)
 assert seen==set(r['project']) and out==set(r['outside']) and r['five_overlap_names']=={n:n in seen for n in five}
 print(root,'project',len(seen),'outside',len(out),'five', {n for n in five if n in seen})
 if root=='DirectBFSBandCarry':
  assert len(seen)==46
  for n in seen:
   assert n in prior and prior[n]['record']['sha256']==proj[n]['.olean']['sha256']
   for s,selected in proj[n].items():
    a=prior[n]['companions'][s];assert (None if a is None else a['sha256'])==(None if selected is None else selected['sha256']),(n,s)
 else:assert len(seen)==208 and {n for n in five if n in seen}==set(five[:2])
assert not j['bfs_producer_conflicts'] and not j['bfs_companion_conflicts'] and not j['bfs_producer_missing']
for n in five[:2]:print(n,proj[n]['.olean']['sha256'],proj[n]['.olean']['path'])
print('PASS: actual recorded outer exit 0; 248 selected projects/28 outside, 192 prior-header hash reuses and 11 fresh header batches, both reachable root sets, all 46 BFS project objects/companions match prior; all selected names/path/hash bundles currently rechecked.')
