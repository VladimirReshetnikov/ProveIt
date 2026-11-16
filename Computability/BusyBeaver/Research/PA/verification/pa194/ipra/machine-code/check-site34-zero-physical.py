#!/usr/bin/env python3
"""Rebuild the literal site-34 entry prefix and model-valued header scan over documented prebuilt stages."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
if len(sys.argv)!=30: raise SystemExit('usage: checker REPO SRC BRANCH34 SECOND TO14 GENERAL FIRST34 POSPHYSICAL POS12 POSRETURN ZEROPHYSICAL TO14 BOUNDARY ZEROFILE BRANCH TO4 TO1 SECONDROOT RETURN FIRSTPASS LOOP MATCHED TAIL CARRY BASELINE FETCH PROJECT PACKAGE OUT')
repo,src,branch34,second,to14stage,general,first34,posphysical,pos12,posreturn,zerophysical,to14,boundary,zerofile,branch,to4,to1,secondroot,returnstage,firstpass,loop,matched,tail,carry,baseline,fetch,project,package,out = [Path(x).resolve() for x in sys.argv[1:]]
if out.exists(): raise SystemExit('Refusing existing output: '+str(out))
for k in ('GIT_DIR','GIT_WORK_TREE','GIT_INDEX_FILE','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES'):
    if k in os.environ: raise SystemExit('Refusing inherited '+k)
receipts=[branch34/'site34-branch-receipt.json',second/'site34-second-pass-receipt.json',to14stage/'site34-to14-receipt.json',general/'site34-first-pass-general-receipt.json',first34/'site34-first-pass-receipt.json',posphysical/'site32-positive-physical-receipt.json',pos12/'site32-positive-returned-receipt.json',posreturn/'site32-positive-return-receipt.json',zerophysical/'site32-zero-physical-receipt.json',to14/'site32-zero-to14-receipt.json',boundary/'site32-zero-boundary-receipt.json',zerofile/'site32-zero-file-receipt.json',branch/'site32-branch-receipt.json',to4/'site32-to4-receipt.json',to1/'site32-to1-receipt.json',secondroot/'site32-second-root-receipt.json',returnstage/'site32-return-header-receipt.json',firstpass/'site32-first-pass-receipt.json',loop/'loop-to32-receipt.json',loop/'matched-loop-extension-receipt.json',matched/'site31-controller-closure-receipt.json',fetch/'source-closure.json']
for p in receipts:
    if not p.is_file(): raise SystemExit('Missing receipt: '+str(p))
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(root,n): return root.joinpath(*n.split('.')).with_suffix('.olean')
machine=repo/'Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code'
names=['PA194Site34ZeroFile','PA194CarryOneAppendZero','PA194Site34ZeroRollback','PA194Site34ZeroBoundary','PA194Site34ZeroBoundaryTo12','PA194Site34ZeroTo12','PA194Site34ZeroTo16','PA194Site34ZeroReturn','PA194Site34ZeroPath','PA194SourceSite34Controller','PA194SourceSite34ZeroPhysical']
paths={n:src/(n+'.lean') for n in names}
for p in paths.values():
    if not p.is_file():raise SystemExit('Missing source '+str(p))
roots=[branch34,second,to14stage,general,first34,posphysical,pos12,posreturn,zerophysical,to14,boundary,zerofile,branch,to4,to1,secondroot,returnstage,firstpass,loop,matched,tail,carry,baseline]
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
    expected = {'PA194Site34ZeroFile':['returnedIsSourceFile'],'PA194CarryOneAppendZero':['oneThenZero'],
      'PA194Site34ZeroRollback':['zeroRollback'],'PA194Site34ZeroBoundary':['zeroToBoundary'],
      'PA194Site34ZeroBoundaryTo12':['fourRows'],'PA194Site34ZeroTo12':['zeroTo12'],
      'PA194Site34ZeroTo16':['zeroTo16'],'PA194Site34ZeroReturn':['returnWord'],
      'PA194Site34ZeroPath':['path42','zeroPath'],'PA194SourceSite34Controller':['site34Instruction','zeroBranch'],
      'PA194SourceSite34ZeroPhysical':['zeroBranch']}
    for theorem in expected.get(n,[]):
        if f"'{n}.{theorem}' depends on axioms:" not in r.stdout:
            raise SystemExit('Missing axiom audit '+n+'.'+theorem)
for name,h in {**base_hash,**source_hash}.items():
    if digest(Path(name))!=h:raise SystemExit('Input changed '+name)
(out/'site34-zero-physical-receipt.json').write_text(json.dumps({'source_sha256':source_hash,'prebuilt_sha256':base_hash,'build_order':names},indent=2)+'\n')
print('PASS: site-34 matched source and physical zero branch; documented stages and foundations remain prebuilt.',flush=True)
