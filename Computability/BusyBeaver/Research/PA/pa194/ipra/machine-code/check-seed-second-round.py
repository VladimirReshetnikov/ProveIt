#!/usr/bin/env python3
"""Replay the blank-seed second decoder round."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
if len(sys.argv)<12:raise SystemExit('usage: checker REPO SRC SEED SEED26 LOOP RESTORE ENTRY FETCH PROJECT PACKAGE OUT [PREREQ_ROOT ...]')
repo,src,seed,seed26,loop,restore,entry,fetch,project,package,out,*extra=[Path(x).resolve() for x in sys.argv[1:]]
if out.exists():raise SystemExit('Refusing existing output: '+str(out))
for k in ('GIT_DIR','GIT_WORK_TREE','GIT_INDEX_FILE','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES'):
    if k in os.environ:raise SystemExit('Refusing inherited '+k)
receipts=[seed26/'input-object-receipt.json',loop/'loop-to32-receipt.json',restore/'site31-restore-physical-exit-receipt.json',entry/'site35-restore-entry-receipt.json',fetch/'source-closure.json']
gap_receipts=[p/'seed-first-gap-receipt.json' for p in extra if (p/'seed-first-gap-receipt.json').is_file()]
if len(gap_receipts)!=1:raise SystemExit('Expected one seed-first-gap receipt')
receipts+=gap_receipts
for p in receipts:
    if not p.is_file():raise SystemExit('Missing receipt '+str(p))
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(root,n):return root.joinpath(*n.split('.')).with_suffix('.olean')
roots=list(dict.fromkeys([seed,seed26,loop,restore,entry,*extra]))
names=['PA194SourcePositiveDecoderSingle','PA194SeedSecondRound']
sources={n:src/(n+'.lean') for n in names}
if not all(p.is_file() for p in sources.values()):raise SystemExit('Missing requested source')
source_hash={str(p):digest(p) for p in sources.values()}
base_hash={str(p):digest(p) for p in receipts}
for n,p in sources.items():
    for line in p.read_text().splitlines():
        m=re.match(r'^\s*import\s+([^/-]+)',line)
        if not m:continue
        for dep in m.group(1).split():
            if dep in names:
                if names.index(dep)>=names.index(n):raise SystemExit('Invalid build order '+n+' '+dep)
                continue
            found=[obj(root,dep) for root in roots if obj(root,dep).exists()]
            if not found and dep.startswith(('PA194','M6.','Packed','Configuration')):raise SystemExit('Missing direct machine import '+dep)
            if len(found)>1 and any(digest(x)!=digest(found[0]) for x in found[1:]):raise SystemExit('Conflicting direct import '+dep+': '+str(found))
            if found:
                for q in [found[0],Path(str(found[0])+'.private'),Path(str(found[0])+'.server')]:
                    if q.exists():base_hash[str(q)]=digest(q)
out.mkdir(parents=True)
lake=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
path=':'.join(map(str,[out,*roots,fetch/'foundation-view',project,package]))+':'+lake
expected={'PA194SourcePositiveDecoderSingle':['positiveSingle'],'PA194SeedSecondRound':['suffix','blankToNext34']}
for n in names:
    dest=out/(n+'.lean');shutil.copyfile(sources[n],dest)
    print('Checking '+n,flush=True)
    r=subprocess.run(['lake','env','env','LEAN_PATH='+path,'lean','-M6000','-j1','-R',str(out),'-o',str(obj(out,n)),str(dest)],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(r.stdout,end='',flush=True)
    if r.returncode or 'sorryAx' in r.stdout:raise SystemExit('Lean audit failed for '+n+', exit '+str(r.returncode))
    for theorem in expected[n]:
        if f"'{n}.{theorem}' depends on axioms:" not in r.stdout:raise SystemExit('Missing axiom audit '+n+'.'+theorem)
for name,h in {**base_hash,**source_hash}.items():
    if digest(Path(name))!=h:raise SystemExit('Input changed '+name)
(out/'seed-second-round-receipt.json').write_text(json.dumps({'source_sha256':source_hash,'prebuilt_sha256':base_hash,'roots':[str(x) for x in roots]},indent=2)+'\n')
print('PASS: blank-seed second decoder round; earlier closures remain prebuilt.')
