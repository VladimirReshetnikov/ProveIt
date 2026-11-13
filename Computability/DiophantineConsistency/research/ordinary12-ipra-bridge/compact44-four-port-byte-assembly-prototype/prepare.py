#!/usr/bin/env python3
"""Guarded single-root union of the four checked symbolic byte recipes."""
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import tempfile

HERE=Path(__file__).resolve().parent
B=HERE.parent
OBS=HERE/'observations/prepare-attempt01'
SPECS=[
 ('beta',B/'compact44-retained-beta-byte-prototype/observations/attempt03/terminal.json',
  Path('/tmp/compact44-retained-beta-byte-author-ap_xzsq2'), 'RetainedBetaBytes',
  'bd1611b2a0a3343d204c558628514b0e7132921a4263429c27b1f296ee03585b',None),
 ('K',B/'compact44-k-byte-recipe-prototype/observations/attempt01/terminal.json',
  Path('/tmp/compact44-k-byte-recipe-y1mp4tiq'), 'CompactKernelByteRecipe',
  '8982509922de9594e9cca21a873efacb9944d0969a20f7d8e104c305c9f8ae19',
  B/'compact44-k-byte-recipe-prototype/observations/prepare-attempt01/manifest.json'),
 ('MC',B/'compact44-low-byte-assembly-attempt2/observations/attempt01/terminal.json',
  Path('/tmp/compact44-low-byte-assembly-xxmulcse'), 'CompactLowByteAssembly',
  '83bf7396f168ed2a4aa49e0e13ec43a7d265f951e26d7c894b66351002e9d098',
  B/'compact44-low-byte-assembly-attempt/observations/prepare-attempt01/manifest.json'),
 ('MF',B/'compact44-mf-byte-assembly-prototype/observations/attempt01/terminal.json',
  Path('/tmp/compact44-mf-byte-assembly-g3jgk09k'), 'CompactShiftedHighByteAssembly',
  '992dd20b27f39d9fda165349221ca1e93ed36789816d48d17555bea74efec77e',
  B/'compact44-mf-byte-assembly-prototype/observations/prepare-attempt01/manifest.json'),
]
SUFFIXES=('.olean.private.hash','.olean.server.hash','.olean.hash','.olean.private',
 '.olean.server','.olean','.ir.hash','.ir','.ilean.hash','.ilean')
def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def record(p):
 p=Path(p)
 if not os.path.lexists(p): return None
 if not p.is_file(): raise RuntimeError(f'dangling {p}')
 return {'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
         'link':os.readlink(p) if p.is_symlink() else None}
def family(n): return next((n[:-len(s)] for s in SUFFIXES if n.endswith(s)),None)
if OBS.exists(): raise RuntimeError('observation exists')
if shutil.disk_usage('/tmp').free<4*1024**3: raise RuntimeError('less than 4 GiB free')
manifests=[]; all_guards={}; extras=[];receipt_pins={}
for name,receipt_path,root,module,expected,manifest_path in SPECS:
 receipt=json.loads(receipt_path.read_text()); receipt_pins[name]=digest(receipt_path)
 if receipt['exit_code']!=0 or not receipt['guards_unchanged'] or receipt['object_sha256']!=expected:
  raise RuntimeError(f'unaccepted receipt: {name}')
 if digest(root/(module+'.olean'))!=expected: raise RuntimeError(f'object drift: {name}')
 if digest(root/(module+'.lean'))!=receipt['source_sha256']:
  raise RuntimeError(f'source drift: {name}')
 log=receipt_path.parent/'compile.log'
 if digest(log)!=receipt['log_sha256'] or any(x in log.read_text() for x in ('error:','warning:','sorryAx')):
  raise RuntimeError(f'log rejected: {name}')
 for path,old in receipt['guards_before'].items():
  if record(path)!=old: raise RuntimeError(f'direct guard drift: {path}')
  if path in all_guards and all_guards[path]!=old: raise RuntimeError(f'guard overlap mismatch: {path}')
  all_guards[path]=old
 extras.append((module+'.olean',root/(module+'.olean')))
 if manifest_path is not None:
  m=json.loads(manifest_path.read_text())
  if receipt['manifest_sha256']!=digest(manifest_path): raise RuntimeError(f'manifest drift: {name}')
  if not m['unchanged'] or not receipt['selected_unchanged'] or not receipt['providers_unchanged']:
   raise RuntimeError(f'prior provider unaccepted: {name}')
  lib=Path(m['project'])/'lib'
  live={p.relative_to(lib).as_posix():record(p) for p in lib.rglob('*') if p.is_file()}
  if set(live)!=set(m['files']) or any(live[k]['sha256']!=m['files'][k]['sha256'] or
      live[k]['resolved']!=m['files'][k]['resolved'] for k in live):
   raise RuntimeError(f'prior selected union drift: {name}')
  for path,old in m['providers_before'].items():
   if record(path)!=old: raise RuntimeError(f'prior provider drift: {path}')
  manifests.append((name,manifest_path,m,lib))
seen={};owners={};conflicts=[];suppressed=[];overlap={}
for name,path,m,lib in manifests:
 for rel,rec0 in m['files'].items():
  fam=family(rel); p=lib/rel; rec={'path':str(p),**record(p)}
  if rel in seen:
   overlap[name]=overlap.get(name,0)+1
   if seen[rel]['sha256']!=rec['sha256']: conflicts.append((rel,seen[rel]['path'],str(p)))
  if fam not in owners: owners[fam]=name
  if owners[fam]!=name and rel not in seen: suppressed.append((name,rel))
  elif owners[fam]==name: seen.setdefault(rel,rec)
for rel,p in extras:
 rec={'path':str(p),**record(p)}
 if rel in seen and seen[rel]['sha256']!=rec['sha256']: conflicts.append((rel,seen[rel]['path'],str(p)))
 seen.setdefault(rel,rec)
if conflicts: raise RuntimeError(f'object conflict: {conflicts[:5]}')
project=Path(tempfile.mkdtemp(prefix='compact44-four-port-byte-assembly-'))
lib=project/'lib';lib.mkdir()
for rel,rec in seen.items():
 p=lib/rel;p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(rec['resolved'])
if any(record(path)!=old for path,old in all_guards.items()): raise RuntimeError('direct guard changed')
for _,_,m,_ in manifests:
 if any(record(path)!=old for path,old in m['providers_before'].items()):
  raise RuntimeError('prior provider changed during preflight')
OBS.mkdir(parents=True)
manifest={'project':str(project),'files':seen,'overlap_counts':overlap,'suppressed_companions':suppressed,
 'guards_before':all_guards,'prior_receipt_sha256':receipt_pins,
 'prior_manifests':{name:{'path':str(path),'sha256':digest(path),'providers_before':m['providers_before']}
                    for name,path,m,_ in manifests},
 'unchanged':True,'scope':'author-side selected union; no file or iPRA theorem'}
(OBS/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps({'project':str(project),'files':len(seen),'overlaps':overlap,
                  'suppressed':len(suppressed),'unchanged':True},sort_keys=True))
