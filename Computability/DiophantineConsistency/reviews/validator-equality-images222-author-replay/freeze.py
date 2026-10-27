import hashlib,json,shutil
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
REV=D/'reviews'
OUT=Path('/tmp/validator-equality-images222-author-5da_pegl')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
last=Path((OUT/'latest-run').read_text().strip())
state=json.loads((last/'state.json').read_text())
require(state['status']=='PASS' and len(state['completed'])==2,'final pair')
data=json.loads((OUT/'inputs.json').read_text())
require(sha(REV/'validator-equality-images222-cache.json')=='82f043a0c34f8ae9fbac8cc15df6d6cb5c0aa06057b33ece0f38434a4d88d3fe','frozen cache')
for r in json.loads((last/'pins.json').read_text())+data['inherited_observations']:
    require(sha(r['path'])==r['sha256'],'final observation '+r['path'])
for r in state['completed']:
    require(sha(r['source'])==r['source_sha256'],'final source')
    require(sha(r['snapshot'])==r['snapshot_sha256'],'final snapshot')
    require(sha(r['object']['path'])==r['object']['sha256'],'final object')
    require(not Path(r['object']['path']).is_symlink(),'regular new object')
    require(sha(r['log'])==r['log_sha256'],'final log')
    require(sha(r['timing'])==r['timing_sha256'],'final timing')
require(Path(state['completed'][0]['log']).read_text()=='','clean main')
require(len(state['completed'][1]['axiom_reports'])==25,'twenty-five audits')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
bundle=REV/'validator-equality-images222-author-replay';require(not bundle.exists(),'freeze path')
bundle.mkdir()
shutil.copytree(OUT/'attempts',bundle/'attempts')
for name in ['prepare','build','freeze']:
    shutil.copy2('/tmp/equality-images222-'+name+'.py',bundle/(name+'.py'))
shutil.copy2('/tmp/validator-equality-images222-plan.py',bundle/'plan.py')
shutil.copy2(OUT/'inputs.json',bundle/'inputs.json')
for r in state['completed']:shutil.copy2(r['source'],bundle/Path(r['source']).name)
for p in (D/'research').glob('validator-equality-images222-plan.*'):
    shutil.copy2(p,bundle/p.name)
manifest=[]
for p in sorted(bundle.rglob('*')):
    if p.is_file():manifest.append({'path':str(p.relative_to(bundle)),'sha256':sha(p),'bytes':p.stat().st_size})
(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
guides=[]
for f in ['R2Fixed','R2Gic','ConstructibleInterpretation']:
    p=ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA'/(f+'.lean')
    guides.append({'path':str(p),'sha256':sha(p),'role':'source proof-pattern guide only; no R2 or ConstructibleInterpretation module imported'})
summary={'status':'PASS',
 'scope':'Actual five fully closed equality sentence images under the C222 Eind encoder, exact ofFinite internal recognizer extraction and genuine equality-subtheory AxOK; literal irreflexivity via Eind and relational vacuity. Uniform arbitrary internal environments/streams. Only the final source-refutation composition assumes ISigma2; finite image proofs use ISigma1. No NativeSet.irAx named binding, full ZFC/native axiom images, runtime or HA endpoint claim.',
 'inputs':data,'input_inventory_sha256':sha(REV/'validator-equality-images222-cache.json'),
 'completed':state['completed'],'final_run':str(last),'observation_count':state['observation_count'],
 'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'development':'Two preserved attempts. First main failed only because the unimported old source guide had supplied nth_two_cons; no output object was accepted. Added a private two-line proof from actual internal nth/adjoin identities, without an old R2 import. Second final main/check pair passed with empty main output, no diagnostics and 25 standard-only axiom reports. Both complete source/check snapshots, drivers, pins, timings and logs remain frozen.',
 'guides':guides}
p=REV/'validator-equality-images222-replay.json';require(not p.exists(),'summary freeze')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'manifest_sha256':sha(bundle/'FILES.json'),
 'files':len(manifest),'observations':state['observation_count'],
 'inherited_observations':len(data['inherited_observations']),
 'sources':[{k:r[k] for k in ['module','source_sha256','seconds','object']} for r in state['completed']]},indent=2))
