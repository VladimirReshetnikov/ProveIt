#!/usr/bin/env python3
"""Explicit post-merge leaf refresh with authenticated cache reuse."""
from pathlib import Path
import hashlib, importlib.util, json, os, re, shutil, subprocess, sys, time, tomllib

ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
HERE=Path(__file__).resolve().parent
REV=ROOT/'Computability/DiophantineConsistency/reviews'
SNAPSHOT='891c86e0b2970feb2b7442420d61c37ee7233ff2'
PARSER=REV/'current-positive-zero2011-closure/plan.py'
PARSER_SHA='fce21bcc246d82485ef1cf99510eedcce4bf9d90e21c0ae34681ea385cac9a34'
CHANGED=['AnnotatedClosure','CurrentControllerData2011','CurrentControllerUnits2011',
 'CurrentDummyMutation2011','CurrentPackingRank2011','CurrentWordOrigin2011',
 'CurrentWordPadding2011','NativeBinaryScale','NativeOuterSeedConstruction',
 'NativePellPower','ObjectDivision','ObjectZeroTest','PrimePowerOrder']

def require(ok,s):
    if not ok: raise RuntimeError(s)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def record(p):
    p=Path(p);return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def verify(r): require(sha(r['path'])==r['sha256'],'Hash drift '+r['path'])
def save(p,d):
    t=p.with_suffix('.tmp');t.write_text(json.dumps(d,indent=2)+'\n');t.replace(p)
def obj(lib,n): return lib.joinpath(*n.split('.')).with_suffix('.olean')
require(sha(PARSER)==PARSER_SHA,'Parser pin')
spec=importlib.util.spec_from_file_location('approved_parser',PARSER)
parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)

def plan():
    oldp=REV/'current-positive-zero2011-refresh/manifest.json'
    old=json.loads(oldp.read_text())
    statep=REV/'current-positive-zero2011-refresh/execution-state.json'
    state=json.loads(statep.read_text());require(state['status']=='PASS','Prior refresh')
    known={x['module']:{'source':x['source'],'object':x.get('prior_object')}for x in old['modules']}
    for x in state['completed']:known[x['module']]={'source':x['source'],'object':x['object']}
    require(all(x['object'] for x in known.values()),'Missing authenticated object')
    decoder=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/DecimalMachine215.lean'
    decoderobj=Path('/tmp/arithmetic215-root-peer-7nbm_glx/DecimalMachine215-aligned.olean')
    require(sha(decoder)=='00e46d6917bb18090027bece970a7ad1bc6eb691bd35c682d4be1a5332f82f80','Decoder source')
    require(sha(decoderobj)=='d3a3e00a4cd47a0a147cf51f35f2dba60266a0790cc118a84b89a7519f2d1a06','Decoder object')
    known['DiophantineConsistency.DecimalMachine215']={'source':record(decoder),'object':record(decoderobj)}
    parent=ROOT/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCorrectedStrong.lean'
    parentobj=Path('/tmp/thirteen-lv-root-peer-ox84rr2w/DiophantineConsistency/ThirteenCorrectedStrong.olean')
    require(sha(parent)=='57729066535acf1909d30ea5de0b4b78e1ac6f1ae11a126e1c2c4526cc546efe','Parent source')
    require(sha(parentobj)=='173937877c7d39e1b5ca952fcf370ec1712d99a6c5fca24671a0e4c118f35210','Parent object')
    known['DiophantineConsistency.ThirteenCorrectedStrong']={'source':record(parent),'object':record(parentobj)}
    roots={x['name']:x.get('srcDir','.')for x in tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib']}
    targets=['DiophantineConsistency.'+n for n in CHANGED]
    for n in CHANGED:
        p=ROOT/roots['DiophantineConsistency']/'DiophantineConsistency'/(n+'Checks.lean')
        if p.exists():targets.append('DiophantineConsistency.'+n+'Checks')
    targets+=['DiophantineConsistency.'+n for n in ['CurrentPositiveZero2011','CurrentPositiveZero2011Checks','ThirteenLVCarrier','ThirteenLVCarrierChecks']]
    focus={}
    for n in ['AnnotatedClosure','NativeBinaryScale','NativePellPower','ObjectDivision','ObjectNumericWire']:
        focus['RefreshFocus.'+n]=ROOT/'Computability/DiophantineConsistency/Lean/checks'/(n+'.lean')
    targets+=list(focus)
    modules={};boundary={};visiting=set()
    def visit(n):
        if n in modules or n in boundary:return
        rel=Path(*n.split('.')).with_suffix('.lean');prefix=n.split('.')[0]
        if n not in focus and prefix not in roots:
            p=next((obj(Path(d),n) for d in old['external_lean_path']if obj(Path(d),n).is_file()),None)
            require(p is not None,'Missing external '+n)
            pre,mark,tail=str(p).partition('/.lake/build/lib/lean/')
            src=Path(pre)/Path(tail).with_suffix('.lean') if mark else Path(old['external_lean_path'][-1]).parent.parent/'src/lean'/rel
            boundary[n]={'module':n,'object':record(p),'companions':[record(Path(str(p)+s))for s in ['.private','.server']if Path(str(p)+s).is_file()],'observed_source':record(src)if src.is_file()else None};return
        require(n not in visiting,'Cycle '+n);visiting.add(n)
        p=focus[n]if n in focus else ROOT/roots[prefix]/rel
        committed=subprocess.check_output(['git','show',SNAPSHOT+':'+str(p.relative_to(ROOT))],cwd=ROOT)
        require(hashlib.sha256(committed).hexdigest()==sha(p),'Snapshot mismatch '+n)
        deps=parser.imports(p)
        for d in deps:visit(d)
        visiting.remove(n)
        fresh=n in targets or n not in known or known[n]['source']['sha256']!=sha(p)
        x={'module':n,'source':record(p),'imports':deps,'action':'fresh'if fresh else 'authenticated_reuse'}
        if not fresh:
            verify(known[n]['object']);x['prior_object']=known[n]['object']
        modules[n]=x
    for n in targets:visit(n)
    m={'scope':'Limited post-merge changed-source/focus/endpoint refresh, not a fresh whole closure',
       'snapshot':SNAPSHOT,'driver':record(__file__),'parser':record(PARSER),
       'prior_evidence':[record(oldp),record(statep)],'toolchain':old['toolchain'],
       'external_lean_path':old['external_lean_path'],'modules':list(modules.values()),'external_boundary':list(boundary.values()),
       'fresh_order':[n for n,x in modules.items()if x['action']=='fresh'],
       'reused_clients_of_fresh':[n for n,x in modules.items()if x['action']!='fresh'and any(d in modules and modules[d]['action']=='fresh'for d in x['imports'])]}
    m['counts']={'custom_total':len(modules),'fresh':len(m['fresh_order']),'reused':len(modules)-len(m['fresh_order']),'external_direct':len(boundary)}
    save(HERE/'manifest.json',m);print(json.dumps(m['counts']));print(sha(HERE/'manifest.json'))

def run(pin,directory):
    mp=HERE/'manifest.json';require(sha(mp)==pin,'Manifest pin');m=json.loads(mp.read_text())
    work=Path(directory).resolve();require(work.parent==Path('/tmp')and work.name.startswith('ha-postmerge-refresh-')and not work.exists(),'New private directory required')
    for x in [m['driver'],m['parser'],*m['prior_evidence'],*m['toolchain']]:verify(x)
    records={x['module']:x for x in m['modules']};boundary={x['module']:x for x in m['external_boundary']}
    for x in records.values():
        verify(x['source'])
        require(parser.imports(Path(x['source']['path']))==x['imports'],'Import drift')
        if x['action']!='fresh':verify(x['prior_object'])
    for x in boundary.values():
        for p in [x['object'],*x['companions']]+([x['observed_source']]if x['observed_source']else []):verify(p)
    require(shutil.disk_usage('/tmp').free>512*2**20,'Disk reserve')
    work.mkdir();lib=work/'lib';lib.mkdir();(work/'logs').mkdir();current={}
    for n,x in records.items():
        if x['action']=='fresh':continue
        p=obj(lib,n);p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(x['prior_object']['path']);current[n]=record(p)
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(lib),*m['external_lean_path']]);env.pop('LEAN_SRC_PATH',None)
    lean=next(x['path']for x in m['toolchain']if x['path'].endswith('/bin/lean'))
    s={'status':'RUNNING','scope':m['scope'],'snapshot':m['snapshot'],'counts':m['counts'],'manifest_sha256':pin,'driver_sha256':sha(__file__),'started':time.time(),'completed':[],'active':None}
    save(work/'state.json',s)
    try:
        for i,n in enumerate(m['fresh_order'],1):
            x=records[n];verify(x['source'])
            for d in x['imports']:verify(current[d]if d in current else boundary[d]['object'])
            require(shutil.disk_usage('/tmp').free>256*2**20,'Disk reserve')
            p=obj(lib,n);p.parent.mkdir(parents=True,exist_ok=True);log=work/'logs'/f'{i:02d}-{n}.txt';timing=log.with_suffix('.time')
            cmd=['/usr/bin/time','-f','elapsed=%e max_rss_kb=%M','-o',str(timing),lean,'-M6000','-j1','-DElab.async=false','-o',str(p),x['source']['path']]
            start=time.time()
            with log.open('w')as out:
                proc=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
                s['active']={'module':n,'pid':proc.pid,'command':cmd,'log':str(log)};save(work/'state.json',s)
                print(json.dumps({'event':'compile',**s['active']}),flush=True);code=proc.wait()
            result={'module':n,'exit_code':code,'seconds':time.time()-start,'command':cmd,'source':x['source'],'log':record(log),'timing':record(timing)}
            s['completed'].append(result);s['active']=None;save(work/'state.json',s)
            require(code==0,'Lean failure '+n+'; '+str(log));verify(x['source'])
            result['object']=record(p);current[n]=result['object']
            reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
            for name,ax in reports:require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},'Extra axiom '+name)
            result['axiom_reports']=reports;save(work/'state.json',s)
            print(json.dumps({'event':'complete','module':n,'seconds':result['seconds'],'reports':len(reports)}),flush=True)
        for n,x in records.items():verify(x['source']);verify(current[n])
        for x in [m['driver'],m['parser'],*m['prior_evidence'],*m['toolchain']]:verify(x)
        for x in boundary.values():
            for p in [x['object'],*x['companions']]+([x['observed_source']]if x['observed_source']else []):verify(p)
        s.update(status='PASS',finished=time.time());save(work/'state.json',s);print(json.dumps({'event':'PASS','counts':m['counts']}),flush=True)
    except BaseException as e:
        s.update(status='FAILED',failure=str(e),finished=time.time());save(work/'state.json',s);raise

if __name__=='__main__':
    if sys.argv[1:]==['plan']:plan()
    elif len(sys.argv)==4 and sys.argv[1]=='run':run(sys.argv[2],sys.argv[3])
    else:raise SystemExit('Use plan, or run MANIFEST_SHA NEW_PRIVATE_DIR')
