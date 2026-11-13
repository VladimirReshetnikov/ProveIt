#!/usr/bin/env python3
"""Bounded object-header scan of the pinned endpoint closure; no theorem build."""
from hashlib import sha256
import json, subprocess, time
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[2]
REPO=HERE.parents[4]
PLAN=HERE.parent/'compact12-ipra-coherent-rebuild-plan'
PREP=HERE.parent/'compact12-ipra-integration-build/observations/attempt01/manifest.json'
PINS=PLAN/'pins.json'
PLANSCAN=PLAN/'scan.json'
HELPER=HERE/'ReadObjectImports.lean'
OUT=HERE/'observations/attempt02'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LIB=Path('/tmp/compact12-ipra-integrated-20261102/lib')
NINE=Path('/tmp/nine-ipra-guarded-author-20261102-h/lib')
EXPECTED_PREP='36ee7a0c7b881cefffafebd7d3a3ff678aec8010ca2019fe71dc8ff8ed29486e'
EXPECTED_PINS='69e58c487a271bd520c371f796f72dcccd8d025105b0909d5a1e425785d39a6d'
EXPECTED_SCAN='a2a217da82e4e330393bd308983c523bace6357813f296f202ad57bfac0a2efa'

def digest(p): return sha256(Path(p).read_bytes()).hexdigest()
def main():
    if OUT.exists(): raise RuntimeError('output exists')
    for path,expected in ((PREP,EXPECTED_PREP),(PINS,EXPECTED_PINS),(PLANSCAN,EXPECTED_SCAN)):
        if digest(path)!=expected: raise RuntimeError(f'pin drift {path}')
    prep=json.loads(PREP.read_text());pins=json.loads(PINS.read_text());plan=json.loads(PLANSCAN.read_text())
    selected=prep['overlay']; modules=pins['modules'];order=pins['order']; helper_hash=digest(HELPER)
    for rel, row in selected.items():
        p=LIB/rel
        if not p.is_file() or digest(p)!=row['sha256'] or str(p.resolve())!=row['resolved']:
            raise RuntimeError(f'overlay drift {rel}')
    actual_overlay={p.relative_to(LIB).as_posix() for p in LIB.rglob('*') if p.is_file()}
    if actual_overlay!=set(selected): raise RuntimeError('overlay file set drift')
    objects={}
    for m in order:
        row=modules[m]; source=REPO/row['path']
        if digest(source)!=row['sha256']: raise RuntimeError(f'source drift {m}')
        rel=m.replace('.','/')+'.olean'; path=LIB/rel
        if not path.is_file(): path=NINE/rel
        if not path.is_file(): raise RuntimeError(f'missing metadata object {m}')
        objects[m]={'path':str(path),'sha256':digest(path),'source_sha256':row['sha256']}
    OUT.mkdir(parents=True)
    inputs=list(objects.items()); logs=[]; actual={}; t0=time.monotonic()
    for start in range(0,len(inputs),12):
        batch=inputs[start:start+12]
        cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER)]+[row['path'] for _,row in batch]
        try:
            run=subprocess.run(cmd,capture_output=True,text=True,timeout=45)
            code,stdout,stderr=run.returncode,run.stdout,run.stderr
        except subprocess.TimeoutExpired as exc:
            code=None; stdout=(exc.stdout or b'').decode() if isinstance(exc.stdout,bytes) else (exc.stdout or '')
            stderr=(exc.stderr or b'').decode() if isinstance(exc.stderr,bytes) else (exc.stderr or '')
        (OUT/f'batch-{start//12:03d}.stdout').write_text(stdout)
        (OUT/f'batch-{start//12:03d}.stderr').write_text(stderr)
        logs.append({'offset':start,'count':len(batch),'command':cmd,'exit_code':code})
        if code!=0 or stderr: break
        paths={row['path']:m for m,row in batch}; current=None
        for line in stdout.splitlines():
            if line.startswith('BEGIN '):
                path=line[6:]
                if current is not None or path not in paths: raise RuntimeError(f'bad BEGIN {line}')
                current=paths[path];actual[current]=[]
            elif line.startswith('IMPORT '):
                if current is None: raise RuntimeError('IMPORT without BEGIN')
                actual[current].append(line[7:])
            elif line=='END':
                if current is None: raise RuntimeError('END without BEGIN')
                current=None
            else: raise RuntimeError(f'unexpected output {line}')
        if current is not None or any(m not in actual for m,_ in batch): raise RuntimeError('incomplete batch output')
        print(json.dumps({'scanned':len(actual),'total':len(inputs)},sort_keys=True),flush=True)
    complete=len(actual)==len(inputs) and all(x['exit_code']==0 for x in logs)
    extra={m:sorted(set(x for x in imports if x.startswith('DiophantineConsistency.'))-set(modules))
      for m,imports in actual.items()}
    extra={m:x for m,x in extra.items() if x}
    differences={m:{'actual_project_imports':sorted(set(x for x in imports if x.startswith('DiophantineConsistency.'))),
      'source_project_imports':sorted(set(modules[m]['imports']))} for m,imports in actual.items()
      if set(x for x in imports if x.startswith('DiophantineConsistency.'))!=set(modules[m]['imports'])}
    # Union source and object edges, never discarding an observed dependency.
    edges={m:set(modules[m]['imports']) | set(x for x in actual.get(m,[]) if x.startswith('DiophantineConsistency.')) for m in order}
    seed=set(plan['endpoint_conflicting_modules']); dirty=set(seed)
    changed=True
    while changed:
        changed=False
        for m in order:
            if m not in dirty and edges[m] & dirty:
                dirty.add(m);changed=True
    missing_dirty=sorted(m for m in dirty if m not in seed and m not in prep['omitted_stale_modules'] and
      (m.replace('.','/')+'.olean' not in prep['selected_files'] or
       Path(prep['selected_files'][m.replace('.','/')+'.olean']['path']).is_relative_to(NINE)))
    after={m:digest(Path(row['path'])) for m,row in objects.items()}
    unchanged=all(after[m]==row['sha256'] and digest(REPO/modules[m]['path'])==row['source_sha256'] for m,row in objects.items())
    overlay_after={p.relative_to(LIB).as_posix():digest(p) for p in LIB.rglob('*') if p.is_file()}
    overlay_unchanged=set(overlay_after)==set(selected) and all(overlay_after[x]==selected[x]['sha256'] for x in selected)
    result={'complete':complete,'objects':objects,'actual_imports':actual,'source_object_import_differences':differences,
      'outside_pinned_source_closure':extra,'dirty_including_conflicts':sorted(dirty),'unplanned_dirty_modules':missing_dirty,
      'objects_and_sources_unchanged':unchanged,'overlay_unchanged':overlay_unchanged,'helper_sha256':helper_hash,
      'helper_unchanged':digest(HELPER)==helper_hash,'batches':logs,'duration_seconds':round(time.monotonic()-t0,3)}
    (OUT/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'complete':complete,'differences':len(differences),'outside':len(extra),
      'dirty_total':len(dirty),'unplanned':len(missing_dirty),'unchanged':unchanged and overlay_unchanged},sort_keys=True),flush=True)
    if not complete or extra or missing_dirty or not unchanged or not overlay_unchanged or digest(HELPER)!=helper_hash:
        raise SystemExit(1)
if __name__=='__main__': main()
