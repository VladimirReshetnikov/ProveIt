#!/usr/bin/env python3
"""Rebuild the site-46 second traversal to control 114 over documented prebuilt stages."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys
if len(sys.argv)<42: raise SystemExit('usage: checker REPO SRC SITE36GAP SITE36ENTRY SITE35PHYS SITE35HEADER SITE35INC SITE35SELECT SITE35TO2 SITE35PASS SITE35TO14 SITE35SECOND SITE35FIRST SITE34POS BRANCH34 SECOND TO14 GENERAL FIRST34 POSPHYSICAL POS12 POSRETURN ZEROPHYSICAL TO14 BOUNDARY ZEROFILE BRANCH TO4 TO1 SECONDROOT RETURN FIRSTPASS LOOP MATCHED TAIL CARRY BASELINE FETCH PROJECT PACKAGE OUT')
repo,src,site36gap,site36entry,site35phys,site35header,site35inc,site35select,site35to2,site35pass,site35to14,site35second,site35first,site34pos,branch34,second,to14stage,general,first34,posphysical,pos12,posreturn,zerophysical,to14,boundary,zerofile,branch,to4,to1,secondroot,returnstage,firstpass,loop,matched,tail,carry,baseline,fetch,project,package,out,*extra = [Path(x).resolve() for x in sys.argv[1:]]
if out.exists(): raise SystemExit('Refusing existing output: '+str(out))
for k in ('GIT_DIR','GIT_WORK_TREE','GIT_INDEX_FILE','GIT_OBJECT_DIRECTORY','GIT_ALTERNATE_OBJECT_DIRECTORIES'):
    if k in os.environ: raise SystemExit('Refusing inherited '+k)
receipts=[site36gap/'site42-positive-physical-receipt.json',site36entry/'site38-to30-receipt.json',site35phys/'site35-source-physical-receipt.json',site35header/'site35-header-return-receipt.json',site35inc/'site35-increment-to7-receipt.json',site35select/'site35-selected-receipt.json',site35to2/'site35-to2-receipt.json',site35pass/'site35-second-pass-receipt.json',site35to14/'site35-to14-receipt.json',site35second/'site35-second-to95-receipt.json',site35first/'site35-first-pass-general-receipt.json',site34pos/'site34-positive-physical-receipt.json',branch34/'site34-branch-receipt.json',second/'site34-second-pass-receipt.json',to14stage/'site34-to14-receipt.json',general/'site34-first-pass-general-receipt.json',first34/'site34-first-pass-receipt.json',posphysical/'site32-positive-physical-receipt.json',pos12/'site32-positive-returned-receipt.json',posreturn/'site32-positive-return-receipt.json',zerophysical/'site32-zero-physical-receipt.json',to14/'site32-zero-to14-receipt.json',boundary/'site32-zero-boundary-receipt.json',zerofile/'site32-zero-file-receipt.json',branch/'site32-branch-receipt.json',to4/'site32-to4-receipt.json',to1/'site32-to1-receipt.json',secondroot/'site32-second-root-receipt.json',returnstage/'site32-return-header-receipt.json',firstpass/'site32-first-pass-receipt.json',loop/'loop-to32-receipt.json',loop/'matched-loop-extension-receipt.json',matched/'site31-controller-closure-receipt.json',fetch/'source-closure.json']
for p in receipts:
    if not p.is_file(): raise SystemExit('Missing receipt: '+str(p))
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(root,n): return root.joinpath(*n.split('.')).with_suffix('.olean')
machine=repo/'Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code'
names=['PA194Site46SecondPrefix','PA194Site46SecondTo95','PA194Site46GapScan','PA194Site46SecondTo114']
paths={n:src/(n+'.lean') for n in names}
for p in paths.values():
    if not p.is_file():raise SystemExit('Missing source '+str(p))
roots=[site36gap,site36entry,site35phys,site35header,site35inc,site35select,site35to2,site35pass,site35to14,site35second,site35first,site34pos,branch34,second,to14stage,general,first34,posphysical,pos12,posreturn,zerophysical,to14,boundary,zerofile,branch,to4,to1,secondroot,returnstage,firstpass,loop,matched,tail,carry,baseline,*extra]
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
    expected = {'PA194Site46SecondPrefix':['prefixWord'],'PA194Site46SecondTo95':['to95'],'PA194Site46GapScan':['scan'],'PA194Site46SecondTo114':['to114']}
    for theorem in expected.get(n,[]):
        if f"'{n}.{theorem}' depends on axioms:" not in r.stdout:
            raise SystemExit('Missing axiom audit '+n+'.'+theorem)
for name,h in {**base_hash,**source_hash}.items():
    if digest(Path(name))!=h:raise SystemExit('Input changed '+name)
(out/'site46-second-to114-receipt.json').write_text(json.dumps({'source_sha256':source_hash,'prebuilt_sha256':base_hash,'build_order':names},indent=2)+'\n')
print('PASS: site-46 second traversal to control 114; documented stages and foundations remain prebuilt.',flush=True)
