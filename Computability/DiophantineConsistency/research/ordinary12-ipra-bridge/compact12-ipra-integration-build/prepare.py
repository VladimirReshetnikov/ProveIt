#!/usr/bin/env python3
"""Prepare a fresh hash-guarded compact-first union; performs no Lean build."""
from hashlib import sha256
import json, os, shutil
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[2]
REPO=HERE.parents[4]
PLAN=HERE.parent/'compact12-ipra-coherent-rebuild-plan'
SCAN=PLAN/'scan.json'
PINS=PLAN/'pins.json'
PRIOR=HERE.parent/'compact44-symbolic-model-unconditional-iff-prototype/observations/attempt01/providers.json'
PRIOR_TERMINAL=HERE.parent/'compact44-symbolic-model-unconditional-iff-prototype/observations/attempt01/terminal.json'
PRIOR_OBJECT=Path('/tmp/compact44-symbolic-model-unconditional-iff-author-d84vdq1g')
NINE=Path('/tmp/nine-ipra-guarded-author-20261102-h/lib')
PROJECT=Path('/tmp/compact12-ipra-integrated-20261102')
OUT=HERE/'observations/attempt01'
EXPECT_SCAN='a2a217da82e4e330393bd308983c523bace6357813f296f202ad57bfac0a2efa'
EXPECT_PINS='69e58c487a271bd520c371f796f72dcccd8d025105b0909d5a1e425785d39a6d'
SUFFIXES=('.olean.private.hash','.olean.server.hash','.olean.hash','.olean.private','.olean.server',
          '.olean','.ir.hash','.ir','.ilean.hash','.ilean')

def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def inventory(roots):
    ret={}
    for root in roots:
        if not root.is_dir(): raise RuntimeError(f'missing root {root}')
        for p in root.rglob('*'):
            if p.is_symlink() and not p.exists(): raise RuntimeError(f'dangling {p}')
            if p.is_file():
                ret[str(p)]={'sha256':digest(p),'resolved':str(p.resolve(strict=True)),
                  'link':os.readlink(p) if p.is_symlink() else None}
    return ret

def main():
    if PROJECT.exists() or PROJECT.is_symlink() or OUT.exists(): raise RuntimeError('output exists')
    if shutil.disk_usage('/tmp').free < 4*1024**3: raise RuntimeError('less than 4 GiB free')
    if digest(SCAN)!=EXPECT_SCAN or digest(PINS)!=EXPECT_PINS: raise RuntimeError('preflight pin drift')
    scan=json.loads(SCAN.read_text()); pins=json.loads(PINS.read_text()); prior=json.loads(PRIOR.read_text()); terminal=json.loads(PRIOR_TERMINAL.read_text())
    if not scan['providers_unchanged'] or not terminal.get('providers_unchanged') or terminal.get('exit_code')!=0:
        raise RuntimeError('prior evidence not successful')
    compact_roots=list(dict.fromkeys(Path(x) for x in prior['roots']))
    if PRIOR_OBJECT not in compact_roots: compact_roots.insert(0,PRIOR_OBJECT)
    before=inventory(compact_roots+[NINE])
    # Existing checked provider paths must still match the checked receipt exactly.
    for path, old in prior['before'].items():
        if before.get(path)!=old: raise RuntimeError(f'checked provider drift {path}')
    obj=PRIOR_OBJECT/'CompactSymbolicModelUnconditionalIff.olean'
    if digest(obj)!=terminal['object_sha256']: raise RuntimeError('unconditional model object drift')
    for name,row in pins['modules'].items():
        if digest(REPO/row['path'])!=row['sha256']: raise RuntimeError(f'source drift {name}')
    for path,value in pins['extra_sources'].items():
        if digest(BASE/path)!=value: raise RuntimeError(f'extra source drift {path}')
    compact={}; compact_conflicts=[]
    for root in compact_roots:
        for p in root.rglob('*'):
            if not p.is_file(): continue
            rel=p.relative_to(root).as_posix(); rec=before[str(p)]
            if rel in compact and compact[rel]['sha256']!=rec['sha256']:
                compact_conflicts.append((rel,compact[rel]['path'],str(p)))
            else: compact.setdefault(rel,{'path':str(p),**rec})
    if compact_conflicts: raise RuntimeError(f'compact conflict {compact_conflicts[:5]}')
    nine={}
    for p in NINE.rglob('*'):
        if p.is_file(): nine[p.relative_to(NINE).as_posix()]={'path':str(p),**before[str(p)]}
    shared=sorted(compact.keys() & nine.keys())
    conflicts={x:{'compact':compact[x]['sha256'],'nine':nine[x]['sha256']} for x in shared
      if compact[x]['sha256']!=nine[x]['sha256']}
    def family(name):
        for suffix in SUFFIXES:
            if name.endswith(suffix): return name[:-len(suffix)]
        return None
    compact_families={family(x) for x in compact if family(x) is not None}
    # Companions stay within a selected module family. Never graft an old
    # nine-base companion onto a compact-selected module.
    selected={name:rec for name,rec in compact.items() if family(name) is not None}
    suppressed=[]
    for name,rec in nine.items():
        f=family(name)
        if f is None: continue
        if f in compact_families:
            if name not in compact: suppressed.append(name)
        else: selected.setdefault(name,rec)
    affected=scan['endpoint_rebuild_after_compact_conflict_override']
    rebuild=[m for m in affected if m.replace('.','/')+'.olean' not in compact]
    removed={}
    for module in rebuild:
        fam=module.replace('.','/')
        keys=[x for x in selected if family(x)==fam]
        if not keys: raise RuntimeError(f'missing old module family {module}')
        for key in keys: removed[key]=selected.pop(key)
    if len(rebuild)!=59: raise RuntimeError(f'unexpected source closure count {len(rebuild)}')
    OUT.mkdir(parents=True)
    PROJECT.mkdir()
    lib=PROJECT/'lib';lib.mkdir()
    for name,rec in selected.items():
        target=lib/name;target.parent.mkdir(parents=True,exist_ok=True)
        target.symlink_to(rec['resolved'])
    overlay={p.relative_to(lib).as_posix():{'sha256':digest(p),'resolved':str(p.resolve(strict=True))}
      for p in lib.rglob('*') if p.is_file()}
    if set(overlay)!=set(selected) or any(overlay[x]['sha256']!=selected[x]['sha256'] for x in selected):
        raise RuntimeError('constructed overlay mismatch')
    after=inventory(compact_roots+[NINE])
    if before!=after: raise RuntimeError('provider changed during preparation')
    if digest(SCAN)!=EXPECT_SCAN or digest(PINS)!=EXPECT_PINS: raise RuntimeError('preflight changed')
    manifest={'scope':'prepared source-pinned overlay; no Lean proof or build',
      'project':str(PROJECT),'provider_roots':[str(x) for x in compact_roots+[NINE]],
      'providers_before':before,'providers_unchanged':before==after,
      'full_shared_count':len(shared),'full_shared_conflicts':conflicts,
      'suppressed_foreign_companions':suppressed,'selected_files':selected,'overlay':overlay,
      'omitted_stale_modules':rebuild,'removed_stale_files':removed,
      'source_pins_sha256':EXPECT_PINS,'source_scan_sha256':EXPECT_SCAN,
      'prior_iff_sha256':terminal['object_sha256']}
    (OUT/'manifest.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'project':str(PROJECT),'selected_files':len(selected),'overlap':len(shared),
      'conflicts':len(conflicts),'omitted_stale_modules':len(rebuild),'providers_unchanged':True},sort_keys=True))
if __name__=='__main__': main()
