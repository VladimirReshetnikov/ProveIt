"""Only two bounded fresh leaf commands, with per-attempt sources and provenance."""
import hashlib,json,os,re,shutil,subprocess,time
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
RUN=Path(Path('/tmp/seed-gic-images222-current.txt').read_text().strip())
I=json.loads((RUN/'inputs.json').read_text())
S=ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA'
NAMES=['ValidatorSeedGicImages222','ValidatorSeedGicImages222Checks']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(ok,msg):
    if not ok: raise RuntimeError(msg)
def reauth():
    observations=[]
    for item in I['inherited_observations']+I['observations']:
        require(sha(item['path'])==item['sha256'],'drift: '+item['path'])
        observations.append(item)
    for item in [I['compiler'],I['toolchain'],I['manifest'],I['plan'],I['plan_manifest']]:
        require(sha(item['path'])==item['sha256'],'drift: '+item['path'])
        observations.append(item)
    return observations
require(shutil.disk_usage('/tmp').free>=512*1024**2,'disk reserve before attempt')
pre=reauth()
A=RUN/'attempts'/str(time.time_ns()); A.mkdir(parents=True)
O=A/'lib';O.mkdir()
# Lean resolves an existing namespace directory in the first root. Each
# attempt therefore contains the approved cache links beside its fresh leaves.
for r in I['modules']:
    for obj in r['objects']:
        stem=r['module'].split('.')[-1]
        relative=r['module'].replace('.','/')+Path(obj['path']).name[len(stem):]
        target=O/relative;target.parent.mkdir(parents=True,exist_ok=True)
        require(not target.exists() and not target.is_symlink(),'existing attempt cache link')
        target.symlink_to(obj['path'])
shutil.copy2(__file__,A/'driver.py');shutil.copy2(RUN/'inputs.json',A/'inputs.json')
sources=[]
for n,expected in zip(NAMES,[['ZFCinPA.ValidatorSeedMarkerRelativization222',
 'ZFCinPA.ValidatorSeedTaggedCollection222','ZFCinPA.NativeGicDelta1','ZFCinPA.NativePeel'],
 ['ZFCinPA.ValidatorSeedGicImages222']]):
    p=S/(n+'.lean');body=p.read_text()
    require(re.findall(r'^import\s+([^\n]+)',body,re.M)==expected,'new import')
    require(not re.search(r'\b(sorry|admit|native_decide)\b',body),'forbidden proof placeholder')
    shutil.copy2(p,A/p.name)
    sources.append({'module':'ZFCinPA.'+n,'path':str(p),'sha256':sha(p),
                    'snapshot':str(A/p.name),'snapshot_sha256':sha(A/p.name)})
state={'status':'RUNNING','private':str(RUN),'attempt':str(A),'sources':sources,
       'pre_observations':pre,'records':[],'driver_sha256':sha(__file__)}
def save(): (A/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();(RUN/'latest-attempt.txt').write_text(str(A)+'\n')
env=dict(os.environ);env['LEAN_PATH']=':'.join([str(O)]+I['package_paths'])
env['LEAN_NUM_THREADS']='1'
for src in sources:
    require(shutil.disk_usage('/tmp').free>=512*1024**2,'disk reserve before leaf')
    require(sha(src['path'])==src['sha256'],'source changed during attempt')
    output=O/(src['module'].replace('.','/')+'.olean')
    output.parent.mkdir(parents=True,exist_ok=True)
    require(not output.exists() and not output.is_symlink(),'output not fresh')
    log=A/(src['module']+'.log');timing=A/(src['module']+'.time')
    command=[I['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(output),src['path']]
    started=time.monotonic()
    with log.open('w') as out:
        result=subprocess.run(['/usr/bin/time','-v','-o',str(timing)]+command,
                              cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT)
    seconds=time.monotonic()-started
    reports=re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log.read_text())
    rec={'module':src['module'],'source':src,'command':command,'exit_code':result.returncode,
         'seconds':seconds,'lean_path':env['LEAN_PATH'],
         'log':{'path':str(log),'sha256':sha(log)},
         'timing':{'path':str(timing),'sha256':sha(timing)},'axiom_reports':reports}
    if output.exists():
        require(not output.is_symlink(),'symlink output')
        rec['object']={'path':str(output),'sha256':sha(output),'bytes':output.stat().st_size}
    state['records'].append(rec);save()
    if result.returncode:
        state['status']='FAILED';break
else:
    clean_main=state['records'][0]['log']['sha256']==hashlib.sha256(b'').hexdigest()
    clean_checks='warning:' not in Path(state['records'][1]['log']['path']).read_text()
    count_ok=len(state['records'][1]['axiom_reports'])==12
    axioms_ok=all(set(re.findall(r'[A-Za-z_][\w.]*',axioms))<=
       {'propext','Classical.choice','Quot.sound'} for _,axioms in state['records'][1]['axiom_reports'])
    state['postchecks']={'clean_main':clean_main,'clean_checks':clean_checks,
      'count_ok':count_ok,'axioms_ok':axioms_ok}
    state['status']='PASS' if all(state['postchecks'].values()) else 'POSTCHECK_FAILED'
state['post_observations']=reauth()
for src in sources:require(sha(src['path'])==src['sha256'],'source changed')
save()
print(json.dumps({'status':state['status'],'attempt':str(A),
                  'records':[{k:r[k] for k in ['module','exit_code','seconds']} for r in state['records']]},indent=2))
