#!/usr/bin/env python3
"""Prepare a guarded object union after all 12 boundary checks; no Lean run."""
from hashlib import sha256
from pathlib import Path
import json
import os
import shutil
import tempfile

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent
BOUNDARIES = BRIDGE/'compact44-low-byte-boundary-chunks'
OBS = HERE/'observations/prepare-attempt01'
FIXED = [
    ('/tmp/compact44-low-byte-recipe-data-author-9s_jncv4', 'CompactLowByteRecipeData', 'a91925db9780268cc67d0a91c12cd6b1b8987e661bb80c2736bfd76001de1320'),
    ('/tmp/compact44-low-byte-window-author-rrt0m6ia', 'CompactLowByteWindow', 'b03192db27e14dc487a1de4307687bb4876fab3dafd4ede9502434becf35e905'),
    ('/tmp/compact44-low-byte-prefix-author-ym79vmqf', 'CompactLowBytePrefix', '4ae4828a3988536838aa0d07cb7ea7814c23166fc4913a148585343e4a8ca84b'),
    ('/tmp/compact44-low-byte-dense-author-9elz2w_8', 'CompactLowByteDense', '6bd153c63fc059cccfd81cf569318105bc8b5725f39033acb6468f4350bd3cd0'),
    ('/tmp/compact44-low-byte-dense-extra-author-l9wwwmlz', 'CompactLowByteDenseExtra', '2754ab0971f602067d726d9f2b5117f8aed0d26027cf5ef7ca810914b3ec15e1'),
    ('/tmp/compact44-low-byte-gaps-author-dgxwcff5', 'CompactLowByteGaps', 'ce69f765958f676f45e375edbe68c025392661cbc7128e970a06a199fd2e9686'),
    ('/tmp/compact44-low-byte-tail-author-tnqj69rp', 'CompactLowByteTail', '8500c38698d2667a57f21231537807b5c872bb0d42b432416abd5c7a5b4e29f4'),
    ('/tmp/compact44-low-byte-bound-author-qki2u_d_', 'CompactLowByteBound', '087cb91ad4dfc367a66a4b090e37140f6d68b1629318a81cfa8ffec233775f49'),
    ('/tmp/generic-radix-window-author-42dtsrv1', 'RadixWindowReconstruction', '0ebcfad8f9de63908c10c280d877c73684b4a98ae41c2ceeddab7914fa8dd62f'),
]
BASE = [Path(x) for x in ['/tmp/ipra-byte-window-generic-01/lib',
    '/tmp/compact44-rank-residue-join-author-6k2xhews', '/tmp/compact44-constructed-rank-author-g2doc30c',
    '/tmp/compact44-packing-origin-mod-four-author-b3v6f92j', '/tmp/compact44-low-mod-four-author-o28oleni',
    '/tmp/ipra-compact44-symbolic-unit-join/lib', '/tmp/ipra-compact-word-cell-author-01/lib']]
SUFFIXES = ('.olean.private.hash', '.olean.server.hash', '.olean.hash', '.olean.private',
            '.olean.server', '.olean', '.ir.hash', '.ir', '.ilean.hash', '.ilean')

def digest(path): return sha256(Path(path).read_bytes()).hexdigest()
def record(p):
    return {'sha256': digest(p), 'resolved': str(p.resolve(strict=True)),
            'link': os.readlink(p) if p.is_symlink() else None}
def family(name):
    return next((name[:-len(s)] for s in SUFFIXES if name.endswith(s)), None)
def inventory(roots):
    return {str(p): record(p) for r in roots for p in r.rglob('*') if p.is_file() and family(p.name)}

if OBS.exists(): raise RuntimeError('observation already exists')
if shutil.disk_usage('/tmp').free < 4*1024**3: raise RuntimeError('less than 4 GiB free')
roots = []
for path, module, expected in FIXED:
    p = Path(path)
    if digest(p/(module+'.olean')) != expected: raise RuntimeError(f'fixed object drift: {module}')
    roots.append(p)
for i in range(1,13):
    module=f'CompactLowByteBoundary{i:02d}'
    receipt_path=BOUNDARIES/'observations'/(module+'-attempt01')/'terminal.json'
    receipt=json.loads(receipt_path.read_text())
    p=Path(receipt['run'])
    if receipt['exit_code'] != 0 or not receipt['guards_unchanged'] or not receipt['generic_unchanged']:
        raise RuntimeError(f'boundary not accepted: {module}')
    if digest(p/(module+'.olean')) != receipt['object_sha256']:
        raise RuntimeError(f'boundary object drift: {module}')
    if digest(BOUNDARIES/(module+'.lean')) != receipt['source_sha256']:
        raise RuntimeError(f'boundary source drift: {module}')
    roots.append(p)
roots += BASE
before=inventory(roots)
seen={}; family_owner={}; conflicts=[]; suppressed=[]
for root in roots:
    for p in root.rglob('*'):
        if not p.is_file(): continue
        rel=p.relative_to(root).as_posix(); fam=family(rel)
        if fam is None: continue
        rec={'path':str(p), **before[str(p)]}
        if rel in seen and seen[rel]['sha256'] != rec['sha256']:
            conflicts.append((rel,seen[rel]['path'],str(p)))
        if fam not in family_owner: family_owner[fam]=root
        if family_owner[fam] != root and rel not in seen:
            suppressed.append(rel)
        elif family_owner[fam] == root:
            seen.setdefault(rel,rec)
if conflicts: raise RuntimeError(f'object conflicts: {conflicts[:5]}')
project=Path(tempfile.mkdtemp(prefix='compact44-low-byte-assembly-'))
lib=project/'lib';lib.mkdir()
for rel,rec in seen.items():
    out=lib/rel;out.parent.mkdir(parents=True,exist_ok=True);out.symlink_to(rec['resolved'])
after=inventory(roots)
if before != after: raise RuntimeError('provider changed during preparation')
OBS.mkdir(parents=True)
manifest={'roots':[str(r) for r in roots], 'files':seen, 'suppressed_companions':suppressed,
          'unchanged':before==after, 'project':str(project),
          'scope':'author-side selected object union, not a Lean proof or complete ancestry audit'}
(OBS/'manifest.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
print(json.dumps({'project':str(project), 'files':len(seen), 'suppressed':len(suppressed),
                  'unchanged':True},sort_keys=True))
