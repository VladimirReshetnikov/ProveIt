import hashlib, json, os, re, shutil, subprocess, sys, time
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
OUT=Path('/tmp/validator-full-seed-theory222-author-ornon89h')
PIN=ROOT/'Computability/DiophantineConsistency/reviews/validator-full-seed-theory222-cache.json'
EXPECTED='f6419623c32fa0870b6dd368fbb2e324cb6a566aea6c38aa5c72d3d71e0c23ad'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
require(sha(PIN)==EXPECTED,'frozen inventory')
data=json.loads(PIN.read_text());OBS=[]
def observe(p,h,tag):
    actual=sha(p);require(actual==h,tag+' '+str(p))
    OBS.append({'path':str(p),'sha256':actual,'role':tag})
def recheck():
    observe(PIN,EXPECTED,'inventory')
    for k in ['compiler','manifest','toolchain']:
        observe(data[k],data[k+'_sha256'],k)
    for p in data['parent_receipts']:observe(p['path'],p['sha256'],'parent receipt')
    for r in data['modules']:
        observe(r['source'],r['source_sha256'],'cached source')
        for o in r['objects']:observe(o['path'],o['sha256'],'cached artifact')
    for r in data['external']:observe(r['path'],r['sha256'],'external boundary')
names=['ZFCinPA.ValidatorFullSeedTheory222','ZFCinPA.ValidatorFullSeedTheory222Checks']
requested=sys.argv[1:] or names
require(all(n in names for n in requested),'only two new leaves')
stamp=str(time.time_ns());run=OUT/'attempts'/stamp;run.mkdir()
shutil.copy2(__file__,run/'driver.py')
env=dict(os.environ,LEAN_PATH=data['lean_path'],LEAN_NUM_THREADS='1')
env.pop('LEAN_SRC_PATH',None)
recheck()
plan=[]
for n in requested:
    p=ROOT/'Logic/Interpretability/ZFCinPA/Lean'/(n.replace('.','/')+'.lean')
    code=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S))
    require(not re.search(r'\b(sorry|native_decide|axiom)\b',code),'no proof shortcuts')
    expected=['ZFCinPA.SchemaClosure','ZFCinPA.ValidatorSourceFullSeed222','ZFCinPA.ValidatorEqualityImages222'] if n==names[0] else [names[0]]
    require(re.findall(r'^import ([\w.]+)$',p.read_text(),re.M)==expected,'exact new imports')
    snapshot=run/p.name;shutil.copy2(p,snapshot)
    plan.append({'module':n,'source':str(p),'source_sha256':sha(p),'snapshot':str(snapshot),'snapshot_sha256':sha(snapshot)})
(run/'plan.json').write_text(json.dumps(plan,indent=2)+'\n')
state={'status':'RUNNING','inputs_sha256':EXPECTED,'inputs':str(PIN),'overlay':str(OUT),'driver_sha256':sha(__file__),'completed':[]}
for r in plan:
    require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
    target=OUT/'lib'/(r['module'].replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
    require(not target.is_symlink(),'new output must not be symlink')
    if target.exists():
        prev=run/(target.name+'.previous');os.link(target,prev);r['previous_object']={'path':str(prev),'sha256':sha(prev)}
        target.unlink()
    log=run/(r['module']+'.log');timing=log.with_suffix('.time')
    command=[data['compiler'],'-M6000','-j1','-DElab.async=false','-o',str(target),r['source']]
    print('START '+r['module'],flush=True);start=time.monotonic()
    with log.open('w') as f:
        result=subprocess.run(['/usr/bin/time','-v','-o',str(timing)]+command,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
    r.update(command=command,exit_code=result.returncode,seconds=time.monotonic()-start,
      log=str(log),log_sha256=sha(log),timing=str(timing),timing_sha256=sha(timing))
    observe(r['source'],r['source_sha256'],'executed source postcheck')
    if result.returncode==0:
        require(target.is_file() and not target.is_symlink(),'regular output')
        r['object']={'path':str(target),'sha256':sha(target),'bytes':target.stat().st_size}
        r['axiom_reports']=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log.read_text(),flags=re.S)
        for theorem,axioms in r['axiom_reports']:
            require(set(re.findall(r'[\w.]+',axioms))<={'propext','Classical.choice','Quot.sound'},'unexpected axiom '+theorem)
    state['completed'].append(r);recheck()
    state['status']='FAIL' if result.returncode else 'RUNNING'
    (run/'state.json').write_text(json.dumps(state,indent=2)+'\n')
    (run/'pins.json').write_text(json.dumps(OBS,indent=2)+'\n')
    print(json.dumps(r),flush=True);print(log.read_text(),flush=True)
    if result.returncode:sys.exit(result.returncode)
state['status']='PASS';state['observation_count']=len(OBS)
(run/'state.json').write_text(json.dumps(state,indent=2)+'\n')
(OUT/'latest-run').write_text(str(run)+'\n')
print('PASS '+str(run),flush=True)
