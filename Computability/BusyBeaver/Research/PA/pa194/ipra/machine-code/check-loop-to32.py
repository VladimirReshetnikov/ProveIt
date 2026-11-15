#!/usr/bin/env python3
"""Rebuild the model-level loop-to-32 closure over the shared site-31 stage."""
from pathlib import Path
import hashlib, json, os, re, shutil, subprocess, sys

repo, src, matched, tail, carry, baseline, fetch, project, package, out = map(Path, sys.argv[1:11])
repo,src,matched,tail,carry,baseline,fetch,project,package,out = (p.resolve() for p in (repo,src,matched,tail,carry,baseline,fetch,project,package,out))
if out.exists(): raise SystemExit('Refusing existing output: '+str(out))
for k in ('GIT_DIR','GIT_WORK_TREE','GIT_INDEX_FILE','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES'):
    if k in os.environ: raise SystemExit('Refusing inherited '+k)
if not (matched/'site31-controller-closure-receipt.json').is_file(): raise SystemExit('Missing matched-stage receipt')
manifest_path=fetch/'source-closure.json'
records=json.loads(manifest_path.read_text())
by_module={r['module']: (Path(r['source']).resolve(),r['sha256']) for r in records}
machine=repo/'Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code'
for p in machine.glob('*.lean'):
    by_module[p.stem]=(p.resolve(),None)
for n in ('PA194ActualPhysicalExit','PA194Site31PhysicalClock','PA194PhysicalLoopTo32','PA194SourceLoopTo32','PA194MatchedLoopTo32'):
    by_module[n]=((src/(n+'.lean')).resolve(),None)
forced={'PA194ActualPhysicalExit','PA194Site31PhysicalClock','PA194PhysicalLoopTo32','PA194SourceLoopTo32','PA194MatchedLoopTo32'}
roots=[matched,tail,carry,baseline]
seen,order,base_hash,source_hash,external=set(),[],{},{},set()
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(root,n): return root.joinpath(*n.split('.')).with_suffix('.olean')
def visit(n):
    if n in seen:return
    seen.add(n)
    if n not in forced:
        found=[obj(r,n) for r in roots if obj(r,n).exists()]
        if len(found)>1 and any(digest(x)!=digest(found[0]) for x in found[1:]):
            raise SystemExit('Conflicting prebuilt object: '+n)
        if found:
            for p in [found[0],Path(str(found[0])+'.private'),Path(str(found[0])+'.server')]:
                if p.exists():base_hash[str(p)]=digest(p)
            return
    rec=by_module.get(n)
    if rec is None:
        if n.startswith(('PA194','M6.','Packed','Configuration')):raise SystemExit('Missing machine source '+n)
        external.add(n);return
    p,expected=rec
    if not p.is_file() or not (p.is_relative_to(repo) or p.is_relative_to(src)):raise SystemExit('Invalid source '+str(p))
    h=digest(p)
    if expected and h!=expected:raise SystemExit('Closure source changed '+str(p))
    source_hash[str(p)]=h
    for line in p.read_text().splitlines():
        m=re.match(r'^\s*import\s+([^/-]+)',line)
        if m:
            for dep in m.group(1).split():visit(dep)
    order.append((n,p))
visit('PA194MatchedLoopTo32')
out.mkdir(parents=True)
lake_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
env=os.environ.copy();env['LEAN_PATH']=':'.join(map(str,[out,matched,tail,carry,baseline,fetch/'foundation-view',project,package]))+':'+lake_path
manifest_hash=digest(manifest_path);matched_receipt_hash=digest(matched/'site31-controller-closure-receipt.json')
print(f'Rebuilding {len(order)} machine modules; {len(base_hash)} baseline artifacts.',flush=True)
for n,p in order:
    dest=out.joinpath(*n.split('.')).with_suffix('.lean');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
    print('Checking',n,flush=True)
    r=subprocess.run(['lake','env','env','LEAN_PATH='+env['LEAN_PATH'],'lean','-M6000','-j1','-R',str(out),'-o',str(obj(out,n)),str(dest)],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(r.stdout,end='',flush=True)
    if r.returncode or 'sorryAx' in r.stdout: raise SystemExit(f'Failed {n}: exit {r.returncode}')
    if n=='PA194MatchedLoopTo32' and "'PA194MatchedLoopTo32.matched' depends on axioms:" not in r.stdout: raise SystemExit('Missing final axiom audit')
for name,h in {**base_hash,**source_hash}.items():
    if digest(Path(name))!=h:raise SystemExit('Input changed: '+name)
if digest(manifest_path)!=manifest_hash or digest(matched/'site31-controller-closure-receipt.json')!=matched_receipt_hash:raise SystemExit('Stage manifest changed')
(out/'loop-to32-receipt.json').write_text(json.dumps({'source_sha256':source_hash,'baseline_object_sha256':base_hash,'external_modules':sorted(external),'build_order':[n for n,p in order], 'fetch_source_manifest_sha256':manifest_hash,'matched_receipt_sha256':matched_receipt_hash},indent=2)+'\n')
print('PASS: model-level matched source/physical loop and site-31 increment to site 32; staged baseline/foundations remain prebuilt.',flush=True)
