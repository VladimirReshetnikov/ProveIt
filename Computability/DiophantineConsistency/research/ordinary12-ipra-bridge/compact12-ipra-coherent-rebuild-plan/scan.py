#!/usr/bin/env python3
"""Source-pinned, read-only conflict and endpoint-closure inventory; no build."""
from hashlib import sha256
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
BASE = HERE.parents[2]
PINS = HERE / 'pins.json'
PINS_HASH = '69e58c487a271bd520c371f796f72dcccd8d025105b0909d5a1e425785d39a6d'
NINE = Path('/tmp/nine-ipra-guarded-author-20261102-h/lib')
COMPACT = Path('/tmp/compact44-halt-rank-overlay-vp7w2rjg')
SEED = Path('/tmp/compact44-outer-pell-rebuild-author-67cozz9f')
WORD = Path('/tmp/ipra-compact-word-cell-author-01/lib')
OUT = HERE / 'scan.json'

def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def inventory(root):
    if not root.is_dir(): raise RuntimeError(f'missing provider {root}')
    ans={}
    for p in root.rglob('*'):
        if p.is_symlink() and not p.exists(): raise RuntimeError(f'dangling path {p}')
        if p.is_file():
            ans[p.relative_to(root).as_posix()]={'sha256':digest(p), 'resolved':str(p.resolve(strict=True))}
    return ans

def main():
    if digest(PINS)!=PINS_HASH: raise RuntimeError('source-pin manifest drift')
    pins=json.loads(PINS.read_text())
    for name, row in pins['modules'].items():
        p=REPO/row['path']
        if digest(p)!=row['sha256']: raise RuntimeError(f'source drift {name}')
    for path, value in pins['extra_sources'].items():
        if digest(BASE/path)!=value: raise RuntimeError(f'extra source drift {path}')
    roots={'nine':NINE,'compact':COMPACT,'seed':SEED,'word':WORD}
    before={name:inventory(root) for name,root in roots.items()}
    pairs={}
    for a,b in [('nine','compact'),('nine','seed'),('nine','word'),('compact','seed'),('compact','word'),('seed','word')]:
        shared=sorted(before[a].keys() & before[b].keys())
        pairs[a+'__'+b]={'overlap':len(shared), 'conflicts':{x:{a:before[a][x]['sha256'],b:before[b][x]['sha256']}
          for x in shared if before[a][x]['sha256']!=before[b][x]['sha256']}}
    for key in ['compact__seed','compact__word','seed__word']:
        if pairs[key]['conflicts']: raise RuntimeError(f'compact provider conflict {key}')
    compact_union={}
    for name in ('seed','compact','word'):
        for path, rec in before[name].items(): compact_union.setdefault(path,rec)
    modules=pins['modules']; order=pins['order']
    def obj(m): return m.replace('.','/')+'.olean'
    differences=[m for m in order if obj(m) in before['nine'] and obj(m) in compact_union and
      before['nine'][obj(m)]['sha256']!=compact_union[obj(m)]['sha256']]
    dirty=set(differences); affected=[]
    for m in order:
        if m in dirty or any(d in dirty for d in modules[m]['imports']):
            dirty.add(m); affected.append(m)
    missing_on_compact=[m for m in order if obj(m) not in compact_union]
    missing_on_nine=[m for m in order if obj(m) not in before['nine']]
    # A stopped source closure for building the endpoint on the compact base.
    seen=set(); compact_rebuild=[]
    def visit(m):
        if m in seen: return
        seen.add(m)
        if obj(m) in compact_union: return
        for d in modules[m]['imports']: visit(d)
        compact_rebuild.append(m)
    for m in pins['targets']: visit(m)
    after={name:inventory(root) for name,root in roots.items()}
    if before!=after: raise RuntimeError('provider changed during scan')
    for name,row in modules.items():
        if digest(REPO/row['path'])!=row['sha256']: raise RuntimeError(f'post-scan source drift {name}')
    if digest(PINS)!=PINS_HASH: raise RuntimeError('source-pin manifest changed during scan')
    result={'scope':'read-only static source-import inventory; no Lean build or proof',
      'pins_sha256':PINS_HASH, 'providers':{k:str(v) for k,v in roots.items()},
      'provider_file_counts':{k:len(v) for k,v in before.items()}, 'providers_before':before,
      'providers_unchanged':before==after,'pairwise':pairs,
      'endpoint_source_closure_count':len(order), 'endpoint_source_closure':order,
      'endpoint_missing_on_nine':missing_on_nine,'endpoint_missing_on_compact':missing_on_compact,
      'endpoint_conflicting_modules':differences, 'endpoint_affected_including_conflicts':affected,
      'endpoint_rebuild_after_compact_conflict_override':[m for m in affected if m not in differences],
      'endpoint_rebuild_on_compact_base':compact_rebuild,
      'external_project_imports':pins['external_project_imports']}
    OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'source_closure':len(order),'conflicting_endpoint_modules':len(differences),
      'affected_after_override':len(affected)-len(differences),'compact_stopped_closure':len(compact_rebuild),
      'nine_missing':len(missing_on_nine),'providers_unchanged':before==after},sort_keys=True))
if __name__=='__main__': main()
