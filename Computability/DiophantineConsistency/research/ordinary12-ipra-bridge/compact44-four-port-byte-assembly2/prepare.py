#!/usr/bin/env python3
"""Add the generic tuple lemma to the guarded four-port selected union."""
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import tempfile

HERE=Path(__file__).resolve().parent;B=HERE.parent
PRIOR=B/'compact44-four-port-byte-assembly-prototype/observations/prepare-attempt01/manifest.json'
PRIOR_HASH='ec3f5afc67e4424d9bd026edf0c4a7e5c8a3cb8817bdc29875e81e3ccfe176c8'
GEN=B/'generic-four-byte-port-prototype/observations/attempt02/terminal.json'
GENROOT=Path('/tmp/generic-four-byte-port-author-uu9cqtmj')
GENHASH='c4cf66185b18c427a3a95ea1be7f2d093456a8bd5eeec58473fde82be4a9abd2'
OBS=HERE/'observations/prepare-attempt01'
def digest(p):return sha256(Path(p).read_bytes()).hexdigest()
def record(p):
 p=Path(p)
 if not os.path.lexists(p):return None
 if not p.is_file():raise RuntimeError(f'dangling {p}')
 return {'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
         'link':os.readlink(p) if p.is_symlink() else None}
if OBS.exists():raise RuntimeError('observation exists')
if shutil.disk_usage('/tmp').free<4*1024**3:raise RuntimeError('less than 4 GiB free')
if digest(PRIOR)!=PRIOR_HASH:raise RuntimeError('prior manifest drift')
m=json.loads(PRIOR.read_text());g=json.loads(GEN.read_text());lib=Path(m['project'])/'lib'
if g['exit_code']!=0 or not g['guards_unchanged'] or g['object_sha256']!=GENHASH:
 raise RuntimeError('generic receipt not accepted')
if digest(GENROOT/'GenericFourBytePorts.olean')!=GENHASH or \
   digest(GENROOT/'GenericFourBytePorts.lean')!=g['source_sha256']:
 raise RuntimeError('generic source/object drift')
log=GEN.parent/'compile.log'
if digest(log)!=g['log_sha256'] or any(w in log.read_text() for w in ('error:','warning:','sorryAx')):
 raise RuntimeError('generic log rejected')
if any(record(p)!=old for p,old in g['guards_before'].items()):raise RuntimeError('generic guard drift')
if any(record(p)!=old for p,old in m['guards_before'].items()):raise RuntimeError('prior guard drift')
for item in m['prior_manifests'].values():
 if digest(item['path'])!=item['sha256'] or any(record(p)!=old for p,old in item['providers_before'].items()):
  raise RuntimeError('prior producer drift')
actual={p.relative_to(lib).as_posix():record(p) for p in lib.rglob('*') if p.is_file()}
if set(actual)!=set(m['files']) or any(actual[k]['sha256']!=m['files'][k]['sha256'] or
   actual[k]['resolved']!=m['files'][k]['resolved'] for k in actual):raise RuntimeError('selected union drift')
rel='GenericFourBytePorts.olean';gobj=GENROOT/rel
if rel in actual and actual[rel]['sha256']!=GENHASH:raise RuntimeError('generic overlap mismatch')
project=Path(tempfile.mkdtemp(prefix='compact44-four-port-byte-assembly2-'));out=project/'lib';out.mkdir()
files={}
for k,v in actual.items():
 p=out/k;p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(v['resolved']);files[k]={'path':str(lib/k),**v}
if rel not in files:
 (out/rel).symlink_to(gobj.resolve(strict=True));files[rel]={'path':str(gobj),**record(gobj)}
if any(record(p)!=old for p,old in g['guards_before'].items()) or \
   any(record(p)!=old for p,old in m['guards_before'].items()):raise RuntimeError('guard changed during preflight')
for item in m['prior_manifests'].values():
 if any(record(p)!=old for p,old in item['providers_before'].items()):raise RuntimeError('provider changed')
OBS.mkdir(parents=True)
m.update({'project':str(project),'files':files,'prior_union_manifest':str(PRIOR),
          'prior_union_sha256':PRIOR_HASH,'generic_receipt':str(GEN),
          'generic_receipt_sha256':digest(GEN),'generic_root':str(GENROOT),
          'generic_object_sha256':GENHASH,'unchanged':True,
          'scope':'author-side union with generic tuple object; no file or iPRA proof'})
(OBS/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
print(json.dumps({'project':str(project),'files':len(files),'generic_overlap':rel in actual,'unchanged':True},sort_keys=True))
