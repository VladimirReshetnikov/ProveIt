#!/usr/bin/env python3
"""Prepare and record a checked object union for the MF byte assembly."""
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import tempfile

HERE=Path(__file__).resolve().parent
OBS=HERE/'observations/prepare-attempt01'
FIXED=[
 ('/tmp/compact44-mf-byte-window-author-wic1abva','CompactShiftedHighByteWindow','ccd3c89e8c4ae8eb573e0484fd5df7bee36601dbadd53493e8a5d2231b052fd6'),
 ('/tmp/compact44-mf-byte-bound-author-5apooad6','CompactShiftedHighBound','e45ba6ff17c94225badb0192e6b8d515d0570de8e73db815061437e228072659'),
 ('/tmp/generic-radix-window-author-42dtsrv1','RadixWindowReconstruction','0ebcfad8f9de63908c10c280d877c73684b4a98ae41c2ceeddab7914fa8dd62f'),
 ('/tmp/compact44-shifted-high-digits-author-2p5ms380','CompactShiftedHighDigits','be4f35d915c5e538aac51f2acd257188f15cb32609f16dc5d56bbd75b3b2beac'),
 ('/tmp/generic-radix-shifted-author-aqd1n6ia','RadixShiftedDigits','b1b24a8da200084184f1e4331fbdfa9390ce1019a6f1c8e05649ba0b67046dac'),
 ('/tmp/ipra-byte-window-generic-01/lib','ByteWindow','efe663c787fade899d9e9dcf7bc83924dd0ec49f63fdc8682c5df3afb45c0961'),
]
BASE=[Path(p) for p in ['/tmp/compact44-rank-residue-join-author-6k2xhews',
 '/tmp/compact44-constructed-rank-author-g2doc30c','/tmp/compact44-packing-origin-mod-four-author-b3v6f92j',
 '/tmp/compact44-low-mod-four-author-o28oleni','/tmp/ipra-compact44-symbolic-unit-join/lib',
 '/tmp/ipra-compact-word-cell-author-01/lib']]
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
project=Path(tempfile.mkdtemp(prefix='compact44-mf-byte-assembly-'))
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
