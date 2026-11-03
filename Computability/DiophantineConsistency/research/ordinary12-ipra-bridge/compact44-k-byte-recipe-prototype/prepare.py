#!/usr/bin/env python3
"""Prepare and record a checked object union for the K byte recipe."""
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import tempfile

HERE=Path(__file__).resolve().parent
OBS=HERE/'observations/prepare-attempt01'
FIXED=[
 ('/tmp/compact44-k-top-digit-explore/lib','TopDigitClean','a7b6d66225ef2ab99942a593cfade9498a5287c1e4e4ef5b66b915f283a1beaf'),
 ('/tmp/ipra-byte-k-specialization-01/lib','SymbolicKernelBytes','6d1a7f883fbda1feb53636cff33cddb4ffb19d946ce0bfeed44dda33c3d236d7'),
 ('/tmp/ipra-sparse-k-family-01/lib','ConcreteSparseDigits','428a1969ed04630e6701bcbbb62961f8eae4b11da08a05fb4c7df88d0019ec20'),
 ('/tmp/generic-radix-window-author-42dtsrv1','RadixWindowReconstruction','0ebcfad8f9de63908c10c280d877c73684b4a98ae41c2ceeddab7914fa8dd62f'),
]
BASE=[Path('/tmp/compact44-k-radix-cert-01/lib')]
SUFFIXES=('.olean.private.hash','.olean.server.hash','.olean.hash','.olean.private',
 '.olean.server','.olean','.ir.hash','.ir','.ilean.hash','.ilean')
def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def record(p): return {'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
                       'link':os.readlink(p) if p.is_symlink() else None}
def family(n): return next((n[:-len(s)] for s in SUFFIXES if n.endswith(s)),None)
def inventory(rs): return {str(p):record(p) for r in rs for p in r.rglob('*') if p.is_file() and family(p.name)}
if OBS.exists(): raise RuntimeError('observation exists')
if shutil.disk_usage('/tmp').free<4*1024**3: raise RuntimeError('less than 4 GiB free')
roots=[]
for path,module,expected in FIXED:
    r=Path(path)
    if digest(r/(module+'.olean'))!=expected: raise RuntimeError(f'object drift {module}')
    roots.append(r)
roots+=BASE
before=inventory(roots);seen={};owners={};conflicts=[];suppressed=[]
for root in roots:
    for p in root.rglob('*'):
        if not p.is_file(): continue
        rel=p.relative_to(root).as_posix();fam=family(rel)
        if fam is None: continue
        rec={'path':str(p),**before[str(p)]}
        if rel in seen and seen[rel]['sha256']!=rec['sha256']:
            conflicts.append((rel,seen[rel]['path'],str(p)))
        if fam not in owners: owners[fam]=root
        if owners[fam]!=root and rel not in seen: suppressed.append(rel)
        elif owners[fam]==root: seen.setdefault(rel,rec)
if conflicts: raise RuntimeError(f'object conflicts: {conflicts[:5]}')
project=Path(tempfile.mkdtemp(prefix='compact44-k-byte-recipe-'))
lib=project/'lib';lib.mkdir()
for rel,rec in seen.items():
    p=lib/rel;p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(rec['resolved'])
after=inventory(roots)
if before!=after: raise RuntimeError('provider changed during preparation')
OBS.mkdir(parents=True)
manifest={'roots':[str(r) for r in roots],'files':seen,'suppressed_companions':suppressed,
          'providers_before':before,'unchanged':True,'project':str(project),
          'scope':'author-side selected object union; no Lean proof or complete ancestry audit'}
(OBS/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
print(json.dumps({'project':str(project),'files':len(seen),'suppressed':len(suppressed),'unchanged':True},sort_keys=True))
