#!/usr/bin/env python3
"""Limited changed-source refresh; deliberately not a fresh current closure."""
from pathlib import Path
import hashlib, importlib.util, json, os, re, shutil, subprocess, sys, time, tomllib

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
HERE = Path(__file__).resolve().parent
SNAPSHOT = '8d1729b5d58e338308f2a6521c7416bd24ebef55'
PRIOR = ROOT/'Computability/DiophantineConsistency/reviews/current-positive-zero2011-closure'
PINS = {'plan.py':'fce21bcc246d82485ef1cf99510eedcce4bf9d90e21c0ae34681ea385cac9a34',
        'manifest.json':'444272b7464611dcc25e4c9ccca84443300a5c54ec8d87d86bc44999131b3a21',
        'execution-state.json':'e43280769624245f9caa2c9f9a85585adfec9ea71f3b0de06d6e35fa6ec44ac9'}
FRESH = ['Representation','ArithmeticRepresentation','ComposeRepresentation','DirectComposition',
         'ArithmeticNonzero','PrimePowerOrder','PrimePowerOrderChecks',
         'CurrentPowerCoordinates2011','CurrentPowerCoordinates2011Checks',
         'WangTiles942PhysicalOrder','WangTiles942PhysicalOrderChecks',
         'CurrentKernelResidues2011','CurrentKernelResidues2011Checks',
         'CurrentPositiveZero2011','CurrentPositiveZero2011Checks']
FRESH = ['DiophantineConsistency.'+n for n in FRESH]

def require(b,s):
    if not b: raise RuntimeError(s)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def record(p):
    p=Path(p); return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def verify(r): require(sha(r['path'])==r['sha256'],'Hash drift: '+r['path'])
def save(p,x):
    t=p.with_suffix('.tmp');t.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n');t.replace(p)
def obj(p,n): return p.joinpath(*n.split('.')).with_suffix('.olean')

for name,h in PINS.items(): require(sha(PRIOR/name)==h,'Prior evidence drift: '+name)
spec=importlib.util.spec_from_file_location('oldparser',PRIOR/'plan.py')
parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
old=json.loads((PRIOR/'manifest.json').read_text())
state=json.loads((PRIOR/'execution-state.json').read_text())
require(state['status']=='PASS','Prior run is not PASS')
oldsource={x['module']:x for x in old['modules']}
oldobjects={x['module']:x for x in state['completed']}

def plan():
    roots={x['name']:x.get('srcDir','.') for x in tomllib.loads((ROOT/'lakefile.toml').read_text())['lean_lib']}
    lean=next(x['path'] for x in old['toolchain'] if x['path'].endswith('/bin/lean'))
    modules={}; external={}; visiting=set()
    def visit(n):
        if n in modules or n in external:return
        rel=Path(*n.split('.')).with_suffix('.lean'); prefix=n.split('.')[0]
        if prefix not in roots:
            p=next((Path(d)/rel.with_suffix('.olean') for d in old['external_lean_path'] if (Path(d)/rel.with_suffix('.olean')).is_file()),None)
            require(p is not None,'Missing external '+n)
            left,marker,right=str(p).partition('/.lake/build/lib/lean/')
            src=Path(left)/Path(right).with_suffix('.lean') if marker else Path(lean).parent.parent/'src/lean'/rel
            external[n]={'module':n,'object':record(p),'companions':[record(Path(str(p)+s)) for s in ('.private','.server') if Path(str(p)+s).is_file()],
                         'source':record(src) if src.is_file() else None}
            return
        require(n not in visiting,'Import cycle '+n);visiting.add(n)
        src=ROOT/roots[prefix]/rel
        committed=subprocess.check_output(['git','show',SNAPSHOT+':'+str(src.relative_to(ROOT))],cwd=ROOT)
        require(hashlib.sha256(committed).hexdigest()==sha(src),'Not approved snapshot: '+n)
        deps=parser.imports(src)
        for d in deps:visit(d)
        visiting.remove(n)
        x={'module':n,'source':record(src),'imports':deps,'action':'fresh' if n in FRESH else 'prior_object_reuse'}
        if n not in FRESH:
            require(n in oldsource and n in oldobjects,'Uninventoried custom dependency '+n)
            require(x['source']['sha256']==oldsource[n]['source']['sha256'],'Changed reused source '+n)
            verify(oldobjects[n]['object'])
            require(not oldobjects[n]['companions'],'Unexpected custom companions '+n)
            x['prior_object']=oldobjects[n]['object']
        modules[n]=x
    # Preserve and authenticate the complete original overlay, but refresh only
    # the explicitly listed modules; unchanged descendants remain reused.
    for n in oldsource:visit(n)
    for n in FRESH:visit(n)
    require(set(FRESH)<=set(modules),'Missing fresh targets')
    m={'scope':'Limited changed-source refresh, NOT a new full-closure validation',
       'snapshot':SNAPSHOT,'root':str(ROOT),'driver':record(__file__),
       'evidence':[record(PRIOR/n) for n in PINS], 'toolchain':old['toolchain'],
       'external_lean_path':old['external_lean_path'],'external_boundary':list(external.values()),
       'modules':list(modules.values()),'fresh_order':FRESH,
       'reused_clients_of_fresh':[n for n,x in modules.items() if x['action']!='fresh' and any(d in FRESH for d in x['imports'])]}
    m['counts']={'fresh':len(FRESH),'reused':len(modules)-len(FRESH),'custom_total':len(modules),'external_direct':len(external)}
    save(HERE/'manifest.json',m);print(json.dumps(m['counts'],indent=2));print(sha(HERE/'manifest.json'))

def run(manifest_hash, directory):
    mp=HERE/'manifest.json';require(sha(mp)==manifest_hash,'Manifest pin mismatch');m=json.loads(mp.read_text())
    for r in m['evidence']+m['toolchain']+[m['driver']]:verify(r)
    subprocess.run(['git','merge-base','--is-ancestor',m['snapshot'],'HEAD'],cwd=ROOT,check=True)
    work=Path(directory).resolve();require(work.parent==Path('/tmp') and work.name.startswith('current-positive-zero2011-refresh-'),'Bad work path')
    require(not work.exists(),'Never silently restart a run');require(shutil.disk_usage('/tmp').free>512*2**20,'Disk reserve')
    records={x['module']:x for x in m['modules']}
    boundary={x['module']:x for x in m['external_boundary']}
    for x in m['modules']:
        verify(x['source']);require(parser.imports(Path(x['source']['path']))==x['imports'],'Import drift')
        for p in m['external_lean_path']:require(not obj(Path(p),x['module']).exists(),'External custom shadow')
        if x['action']!='fresh':verify(x['prior_object'])
    for x in boundary.values():
        for r in [x['object']]+x['companions']+([x['source']] if x['source'] else []):verify(r)
    work.mkdir();lib=work/'lib';lib.mkdir();(work/'logs').mkdir()
    current={}
    for n,x in records.items():
        if x['action']=='fresh':continue
        p=obj(lib,n);p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(x['prior_object']['path']);current[n]=record(p)
    env=os.environ.copy();env['LEAN_PATH']=os.pathsep.join([str(lib)]+m['external_lean_path']);env.pop('LEAN_SRC_PATH',None)
    lean=next(x['path'] for x in m['toolchain'] if x['path'].endswith('/bin/lean'))
    s={'status':'RUNNING','scope':m['scope'],'snapshot':m['snapshot'],'started_unix':time.time(),
       'driver_sha256':sha(__file__),'manifest_sha256':sha(mp),'counts':m['counts'],'lean_path':env['LEAN_PATH'],'completed':[],'active':None}
    save(work/'state.json',s)
    try:
        for i,n in enumerate(m['fresh_order'],1):
            x=records[n];verify(x['source'])
            for d in x['imports']:verify(current[d] if d in current else boundary[d]['object'])
            require(shutil.disk_usage('/tmp').free>256*2**20,'Disk reserve')
            output=obj(lib,n);output.parent.mkdir(parents=True,exist_ok=True)
            log=work/'logs'/f'{i:02d}-{n}.log';timing=log.with_suffix('.time')
            cmd=['/usr/bin/time','-f','elapsed=%e max_rss_kb=%M','-o',str(timing),lean,'-M6000','-j1','-DElab.async=false','-o',str(output),x['source']['path']]
            start=time.time()
            with log.open('w') as out:
                p=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
                s['active']={'module':n,'pid':p.pid,'command':cmd,'log':str(log)};save(work/'state.json',s)
                print(json.dumps({'event':'compile',**s['active']}),flush=True);code=p.wait()
            result={'module':n,'exit_code':code,'seconds':time.time()-start,'source':x['source'],'log':record(log),'timing':record(timing)}
            require(code==0,'Lean failure '+n+'; '+str(log));verify(x['source'])
            for d in x['imports']:verify(current[d] if d in current else boundary[d]['object'])
            result['object']=record(output);current[n]=result['object']
            text=log.read_text();reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text)
            for name,axioms in reports:
                require(set(re.findall(r'[A-Za-z][A-Za-z.]*',axioms))<={'propext','Classical.choice','Quot.sound'},'Unexpected axiom '+name)
            result['axiom_reports']=reports;s['completed'].append(result);s['active']=None;save(work/'state.json',s)
            print(json.dumps({'event':'complete','module':n,'seconds':result['seconds'],'reports':len(reports)}),flush=True)
        for n,x in records.items():verify(x['source']);verify(current[n])
        for r in m['evidence']+m['toolchain']+[m['driver']]:verify(r)
        for x in boundary.values():
            for r in [x['object']]+x['companions']+([x['source']] if x['source'] else []):verify(r)
        require(len(s['completed'][-1]['axiom_reports'])==6,'Endpoint report count')
        s.update(status='PASS',finished_unix=time.time());save(work/'state.json',s);print(json.dumps({'event':'PASS','counts':m['counts']}),flush=True)
    except BaseException as e:
        s.update(status='FAILED',finished_unix=time.time(),failure=str(e));save(work/'state.json',s);raise

if __name__=='__main__':
    if sys.argv[1:]==['plan']:plan()
    elif len(sys.argv)==4 and sys.argv[1]=='run':run(sys.argv[2],sys.argv[3])
    else:raise SystemExit('Use plan, or run MANIFEST_SHA UNIQUE_TMP_DIR')
