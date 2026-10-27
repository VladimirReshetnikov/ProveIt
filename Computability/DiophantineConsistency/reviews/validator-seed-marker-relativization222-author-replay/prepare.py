"""Prepare only the approved private source-pinned marker transport closure."""
import hashlib, json, shutil, tempfile
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
PLAN=D/'research/validator-seed-marker-integration-plan.json'
MF=D/'research/validator-seed-marker-integration-FILES.json'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(p,msg):
    if not p: raise RuntimeError(msg)
def pin(p,h):
    require(sha(p)==h,'drift: '+str(p))
    return {'path':str(p),'sha256':h}
require(shutil.disk_usage('/tmp').free>=512*1024**2,'disk reserve')
pin(PLAN,'37aa5cc528c0dd4de6cde821a76610f9ddc055a9b5aace5690706b5688003cc1')
pin(MF,'e4629a6f2fe31a286f2656fcf4116691d5f2baee7fd196e9cb173758aaf1e539')
plan=json.loads(PLAN.read_text()); branch=plan['branches']['recommended_raw_marker_transport']
observations=[]
for r in json.loads(MF.read_text())['files']:
    observations.append(pin(MF.parent/r['path'],r['sha256']))
for r in plan['observations']:
    observations.append(pin(r['path'],r['sha256']))
require(branch['counts']=={'cached_modules':203,'foundation':136,'artifacts':611,
                          'external_boundaries':45,'artifact_providers':656},'scope')
run=Path(tempfile.mkdtemp(prefix='validator-seed-marker-relativization222-author-'))
lib=run/'lib';lib.mkdir()
for r in branch['modules_dependency_order']:
    observations.append(pin(r['source'],r['source_sha256']))
    for obj in r['objects']:
        observations.append(pin(obj['path'],obj['sha256']))
        stem=r['module'].split('.')[-1]
        rel=r['module'].replace('.','/')+Path(obj['path']).name[len(stem):]
        target=lib/rel;target.parent.mkdir(parents=True,exist_ok=True)
        require(not target.exists() and not target.is_symlink(),'existing cache link')
        target.symlink_to(obj['path'])
for r in branch['actual_first_artifact_providers']:
    observations.append(pin(r['path'],r['sha256']))
inputs={'status':'AUTHENTICATED_PREPARE_ONLY','plan':pin(PLAN,sha(PLAN)),
        'plan_manifest':pin(MF,sha(MF)),'counts':branch['counts'],
        'modules':branch['modules_dependency_order'],'external':branch['external'],
        'package_paths':branch['existing_search_path'][1:],
        'compiler':plan['compiler'],'toolchain':plan['toolchain'],'manifest':plan['manifest'],
        'inherited_observations':plan['observations'],
        'observations':observations,'lib':str(lib),'private':str(run),
        'driver':{'path':__file__,'sha256':sha(__file__)},
        'scope':'203 cached/136 Foundation, zero refresh; two new leaves only; accepted Marker peer.'}
(run/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
shutil.copy2(__file__,run/'prepare.py')
Path('/tmp/seed-marker-relativization222-current.txt').write_text(str(run)+'\n')
print(json.dumps({'private':str(run),'inputs_sha256':sha(run/'inputs.json'),
                  'observations':len(observations)},indent=2))
