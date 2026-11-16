#!/usr/bin/env python3
"""Incrementally replay the PRA-model restore-to-site-35 entry composition."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
if len(sys.argv)<10: raise SystemExit('usage: checker REPO SRC RESTORE SITE35 PHYS34 FETCH PROJECT PACKAGE OUT [PREREQ_ROOT ...]')
repo,src,restore,site35,phys34,fetch,project,package,out,*extra = [Path(x).resolve() for x in sys.argv[1:]]
if out.exists(): raise SystemExit('Refusing existing output: '+str(out))
for k in ('GIT_DIR','GIT_WORK_TREE','GIT_INDEX_FILE','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES'):
    if k in os.environ: raise SystemExit('Refusing inherited '+k)
receipts=[restore/'site31-restore-physical-exit-receipt.json',site35/'site35-source-physical-receipt.json',phys34/'site34-positive-physical-receipt.json',fetch/'source-closure.json']
for p in receipts:
    if not p.is_file():raise SystemExit('Missing receipt '+str(p))
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(root,n):return root.joinpath(*n.split('.')).with_suffix('.olean')
source=src/'PA194Site35RestoreEntry.lean'
if not source.is_file():raise SystemExit('Missing source '+str(source))
roots=list(dict.fromkeys([restore,site35,phys34,*extra]))
base_hash={str(p):digest(p) for p in receipts}
for line in source.read_text().splitlines():
    m=re.match(r'^\s*import\s+([^/-]+)',line)
    if not m:continue
    for dep in m.group(1).split():
        found=[obj(root,dep) for root in roots if obj(root,dep).exists()]
        if not found and dep.startswith(('PA194','M6.','Packed','Configuration')):raise SystemExit('Missing direct machine import '+dep)
        if len(found)>1 and any(digest(x)!=digest(found[0]) for x in found[1:]):raise SystemExit('Conflicting direct import '+dep+': '+str(found))
        if found:
            for p in [found[0],Path(str(found[0])+'.private'),Path(str(found[0])+'.server')]:
                if p.exists():base_hash[str(p)]=digest(p)
sh=digest(source)
out.mkdir(parents=True)
lake=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
path=':'.join(map(str,[out,*roots,fetch/'foundation-view',project,package]))+':'+lake
dest=out/source.name;shutil.copyfile(source,dest)
r=subprocess.run(['lake','env','env','LEAN_PATH='+path,'lean','-M6000','-j1','-R',str(out),'-o',str(obj(out,'PA194Site35RestoreEntry')),str(dest)],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
print(r.stdout,end='',flush=True)
if r.returncode or 'sorryAx' in r.stdout:raise SystemExit('Lean audit failed, exit '+str(r.returncode))
if "'PA194Site35RestoreEntry.restoreFeedsSite35' depends on axioms:" not in r.stdout:raise SystemExit('Missing axiom audit')
if digest(source)!=sh:raise SystemExit('Source changed during build')
for name,h in base_hash.items():
    if digest(Path(name))!=h:raise SystemExit('Input changed '+name)
(out/'site35-restore-entry-receipt.json').write_text(json.dumps({'source_sha256':sh,'prebuilt_sha256':base_hash,'roots':[str(x) for x in roots]},indent=2)+'\n')
print('PASS: PRA-model restore to positive site-35 physical entry; earlier closures remain prebuilt.')
