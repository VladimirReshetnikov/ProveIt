#!/usr/bin/env python3
"""Check and merge the exact byte-tuple and retained-shift model providers."""
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import tempfile

HERE=Path(__file__).resolve().parent; B=HERE.parent
BYTE_M=B/'compact44-four-port-byte-assembly2/observations/prepare-attempt01/manifest.json'
BYTE_T=B/'compact44-four-port-byte-assembly2/observations/attempt01/terminal.json'
MODEL_P=B/'free-j-retained-shift-model-prototype/observations/attempt01/providers.json'
MODEL_T=B/'free-j-retained-shift-model-prototype/observations/attempt01/terminal.json'
PINS={BYTE_M:'14edb04f5ec3bf572cf8a1cf07c35a80d0ac0b5726c3e4affac6797d57d82c42',
 BYTE_T:'fefbdac8ff8fa29f147bbc48ce0c8f1097ded1477c51086bd6649634b5250ea4',
 MODEL_P:'6310db877cc8f41d58c9709ff67081ff6f8710ed0c50a23fdc5b84eea4dbcb3a',
 MODEL_T:'84d60b5823e2f794a620830772ba15357f16f384306690a40cb2fc22742749d9'}
BYTE_ROOT=Path('/tmp/compact44-four-port-byte-assembly2-bdss6bu0')
MODEL_ROOT=Path('/tmp/free-j-retained-shift-model-author-tn5e1136')
BYTE_OBJ='0f921668ce8407f4a28346a85e2023d131fc4421e00c790048ac2d813f8e3a85'
MODEL_OBJ='297685a6eb31af3b6c7798baa8f42f168c4c60c5b4a84923f0622cbea07ca485'
OBS=HERE/'observations/prepare-attempt01'
SUFFIXES=('.olean.private.hash','.olean.server.hash','.olean.hash','.olean.private',
 '.olean.server','.olean','.ir.hash','.ir','.ilean.hash','.ilean')
def digest(p):return sha256(Path(p).read_bytes()).hexdigest()
def record(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 if not p.is_file():raise RuntimeError(f'dangling {p}')
 return {'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
         'link':os.readlink(p) if p.is_symlink() else None}
def family(n):return next((n[:-len(s)] for s in SUFFIXES if n.endswith(s)),None)
def inv(roots):return {str(p):record(p) for r in roots for p in r.rglob('*') if p.is_file()}
def byte_live(m):
 lib=Path(m['project'])/'lib'; live={p.relative_to(lib).as_posix():record(p) for p in lib.rglob('*') if p.is_file()}
 return set(live)==set(m['files']) and all(live[k]['sha256']==m['files'][k]['sha256'] and
   live[k]['resolved']==m['files'][k]['resolved'] for k in live)
if OBS.exists():raise RuntimeError('observation exists')
if shutil.disk_usage('/tmp').free<4*1024**3:raise RuntimeError('less than 4 GiB free')
for p,h in PINS.items():
 if digest(p)!=h:raise RuntimeError(f'pin drift {p}')
bm=json.loads(BYTE_M.read_text());bt=json.loads(BYTE_T.read_text())
mp=json.loads(MODEL_P.read_text());mt=json.loads(MODEL_T.read_text())
if bt['exit_code']!=0 or not all(bt[k] for k in ('guards_unchanged','selected_unchanged','producers_unchanged')):
 raise RuntimeError('byte tuple receipt not accepted')
if mt['exit_code']!=0 or not all(mt[k] for k in ('dependencies_unchanged','providers_unchanged','source_unchanged')):
 raise RuntimeError('model receipt not accepted')
for root,module,expected,r in [(BYTE_ROOT,'CompactFourPortByteAssembly2',BYTE_OBJ,bt),
                                (MODEL_ROOT,'FreeJRetainedShiftModel',MODEL_OBJ,mt)]:
 if digest(root/(module+'.olean'))!=expected or r['object_sha256']!=expected or \
    digest(root/(module+'.lean'))!=r['source_sha256']:
  raise RuntimeError(f'source/object drift {module}')
for path,old in bt['guards_before'].items():
 if record(path)!=old:raise RuntimeError(f'byte direct guard drift {path}')
for path,old in mt['dependencies_before'].items():
 if record(path)!=old:raise RuntimeError(f'model direct guard drift {path}')
for item in bm['prior_manifests'].values():
 if digest(item['path'])!=item['sha256'] or any(record(p)!=v for p,v in item['providers_before'].items()):
  raise RuntimeError('byte inherited provider drift')
if not byte_live(bm):raise RuntimeError('byte selected union drift')
roots=[Path(x) for x in mp['roots']]; before=inv(roots)
if before!=mp['before'] or mp['conflicts']:raise RuntimeError('model provider drift/conflict')
seen={};owners={};conflicts=[];suppressed=[];overlap=0
def add(rel,path,owner):
 global overlap
 fam=family(rel)
 if fam is None:return
 rec={'path':str(path),**record(path)}
 if rel in seen:
  overlap+=1
  if seen[rel]['sha256']!=rec['sha256']:conflicts.append((rel,seen[rel]['path'],str(path)))
 if fam not in owners:owners[fam]=owner
 if owners[fam]!=owner and rel not in seen:suppressed.append((owner,rel))
 elif owners[fam]==owner:seen.setdefault(rel,rec)
byte_lib=Path(bm['project'])/'lib'
for rel in bm['files']:add(rel,byte_lib/rel,'byte-union')
for root in roots:
 for p in root.rglob('*'):
  if p.is_file():add(p.relative_to(root).as_posix(),p,str(root))
for root,module in [(BYTE_ROOT,'CompactFourPortByteAssembly2'),(MODEL_ROOT,'FreeJRetainedShiftModel')]:
 add(module+'.olean',root/(module+'.olean'),str(root))
if conflicts:raise RuntimeError(f'object conflicts: {conflicts[:5]}')
project=Path(tempfile.mkdtemp(prefix='compact44-byte-ports-model-iff-'));lib=project/'lib';lib.mkdir()
for rel,rec in seen.items():
 p=lib/rel;p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(rec['resolved'])
if inv(roots)!=before or not byte_live(bm):raise RuntimeError('provider changed during preflight')
if any(record(p)!=v for p,v in bt['guards_before'].items()) or \
   any(record(p)!=v for p,v in mt['dependencies_before'].items()):raise RuntimeError('direct guard changed')
for p,h in PINS.items():
 if digest(p)!=h:raise RuntimeError(f'pin changed {p}')
OBS.mkdir(parents=True)
manifest={'project':str(project),'files':seen,'overlap_count':overlap,'suppressed_companions':suppressed,
 'model_roots':[str(x) for x in roots],'model_before':before,'byte_manifest_path':str(BYTE_M),
 'byte_manifest_sha256':PINS[BYTE_M],'byte_receipt_path':str(BYTE_T),'byte_receipt_sha256':PINS[BYTE_T],
 'model_receipt_path':str(MODEL_T),'model_receipt_sha256':PINS[MODEL_T],
 'byte_guards':bt['guards_before'],'model_guards':mt['dependencies_before'],'unchanged':True,
 'scope':'mixed-provider source-pinned union; not a file or iPRA proof'}
(OBS/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps({'project':str(project),'files':len(seen),'overlaps':overlap,
                  'suppressed':len(suppressed),'model_files':len(before),'unchanged':True},sort_keys=True))
