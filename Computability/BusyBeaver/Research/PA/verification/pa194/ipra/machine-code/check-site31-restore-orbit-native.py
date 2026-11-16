#!/usr/bin/env python3
"""Rebuild the coded-time matched site-31 transfer step over documented prebuilt stages."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
if len(sys.argv)!=35: raise SystemExit('usage: checker REPO SRC ORBIT FULLY RESTORE TRANSFER CODEDLOOP CODE31 NATIVE CODE32 EXACT JUMP POSPHYSICAL POS12 POSRETURN ZEROPHYSICAL TO14 BOUNDARY ZEROFILE BRANCH TO4 TO1 SECONDROOT RETURN FIRSTPASS LOOP MATCHED TAIL CARRY BASELINE FETCH PROJECT PACKAGE OUT')
repo,src,orbit,fully,restore,transfer,codedloop,code31,native,code32,exact,jump,posphysical,pos12,posreturn,zerophysical,to14,boundary,zerofile,branch,to4,to1,secondroot,returnstage,firstpass,loop,matched,tail,carry,baseline,fetch,project,package,out = [Path(x).resolve() for x in sys.argv[1:]]
if out.exists(): raise SystemExit('Refusing existing output: '+str(out))
for k in ('GIT_DIR','GIT_WORK_TREE','GIT_INDEX_FILE','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES'):
    if k in os.environ: raise SystemExit('Refusing inherited '+k)
receipts=[orbit/'site31-restore-physical-orbit-receipt.json',fully/'site31-fully-coded-receipt.json',restore/'site31-restore-iteration-receipt.json',transfer/'site31-transfer-loop-receipt.json',codedloop/'site31-coded-loop-receipt.json',code31/'site31-coded-clock-receipt.json',native/'site31-native-receipt.json',code32/'site32-positive-clock-code-receipt.json',exact/'site32-positive-exact-receipt.json',jump/'site33-jump-receipt.json',posphysical/'site32-positive-physical-receipt.json',pos12/'site32-positive-returned-receipt.json',posreturn/'site32-positive-return-receipt.json',zerophysical/'site32-zero-physical-receipt.json',to14/'site32-zero-to14-receipt.json',boundary/'site32-zero-boundary-receipt.json',zerofile/'site32-zero-file-receipt.json',branch/'site32-branch-receipt.json',to4/'site32-to4-receipt.json',to1/'site32-to1-receipt.json',secondroot/'site32-second-root-receipt.json',returnstage/'site32-return-header-receipt.json',firstpass/'site32-first-pass-receipt.json',loop/'loop-to32-receipt.json',loop/'matched-loop-extension-receipt.json',matched/'site31-controller-closure-receipt.json',fetch/'source-closure.json']
for p in receipts:
    if not p.is_file(): raise SystemExit('Missing receipt: '+str(p))
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(root,n): return root.joinpath(*n.split('.')).with_suffix('.olean')
machine=repo/'Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code'
names=['PA194RestorePhysicalOrbitCode','PA194RestorePhysicalOrbitSentence']
paths={n:src/(n+'.lean') for n in names}
for p in paths.values():
    if not p.is_file():raise SystemExit('Missing source '+str(p))
roots=[orbit,fully,restore,transfer,codedloop,code31,native,code32,exact,jump,posphysical,pos12,posreturn,zerophysical,to14,boundary,zerofile,branch,to4,to1,secondroot,returnstage,firstpass,loop,matched,tail,carry,baseline]
source_hash={str(p):digest(p) for p in paths.values()}
base_hash={str(p):digest(p) for p in receipts}
for n,p in paths.items():
    for line in p.read_text().splitlines():
        m=re.match(r'^\s*import\s+([^/-]+)',line)
        if not m: continue
        for dep in m.group(1).split():
            if dep in names:
                if names.index(dep)>=names.index(n):raise SystemExit('Invalid build order '+n+' '+dep)
                continue
            found=[obj(root,dep) for root in roots if obj(root,dep).exists()]
            if len(found)>1 and any(digest(x)!=digest(found[0]) for x in found[1:]):
                raise SystemExit('Conflicting direct import '+dep+': '+str(found))
            if not found and dep.startswith(('PA194','M6.','Packed','Configuration')):
                raise SystemExit('Missing machine import '+dep)
            if found:
                for q in [found[0],Path(str(found[0])+'.private'),Path(str(found[0])+'.server')]:
                    if q.exists():base_hash[str(q)]=digest(q)
out.mkdir(parents=True)
lake_path=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,text=True).strip()
lean_path=':'.join(map(str,[out,*roots,fetch/'foundation-view',project,package]))+':'+lake_path
for n in names:
    dest=out/(n+'.lean');shutil.copyfile(paths[n],dest)
    print('Checking',n,flush=True)
    r=subprocess.run(['lake','env','env','LEAN_PATH='+lean_path,'lean','-M6000','-j1','-R',str(out),'-o',str(obj(out,n)),str(dest)],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    print(r.stdout,end='',flush=True)
    if r.returncode or 'sorryAx' in r.stdout:raise SystemExit(f'Failed {n}: exit {r.returncode}')
    expected = {'PA194RestorePhysicalOrbitCode':['completeLoop'],
                'PA194RestorePhysicalOrbitSentence':['modelSentence','classicalPRA','nativeIPRA']}
    for theorem in expected.get(n,[]):
        if f"'{n}.{theorem}' depends on axioms:" not in r.stdout:
            raise SystemExit('Missing axiom audit '+n+'.'+theorem)
for name,h in {**base_hash,**source_hash}.items():
    if digest(Path(name))!=h:raise SystemExit('Input changed '+name)
(out/'site31-restore-orbit-native-receipt.json').write_text(json.dumps({'source_sha256':source_hash,'prebuilt_sha256':base_hash,'build_order':names},indent=2)+'\n')
print('PASS: site-31 source and physical transfer loop; documented stages and foundations remain prebuilt.',flush=True)
