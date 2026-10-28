import hashlib,json,shutil
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
REV=D/'reviews'
OUT=Path('/tmp/validator-full-seed-theory222-author-ornon89h')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
last=Path((OUT/'latest-run').read_text().strip())
state=json.loads((last/'state.json').read_text())
require(state['status']=='PASS' and len(state['completed'])==2,'final pair')
data=json.loads((OUT/'inputs.json').read_text())
cache=REV/'validator-full-seed-theory222-cache.json'
require(sha(cache)=='f6419623c32fa0870b6dd368fbb2e324cb6a566aea6c38aa5c72d3d71e0c23ad','frozen cache')
for r in json.loads((last/'pins.json').read_text())+data['inherited_observations']:
    require(sha(r['path'])==r['sha256'],'final observation '+r['path'])
for r in state['completed']:
    for p,h in [(r['source'],r['source_sha256']),(r['snapshot'],r['snapshot_sha256']),
      (r['object']['path'],r['object']['sha256']),(r['log'],r['log_sha256']),
      (r['timing'],r['timing_sha256'])]:require(sha(p)==h,'final artifact '+p)
    require(not Path(r['object']['path']).is_symlink(),'regular new object')
require(Path(state['completed'][0]['log']).read_text()=='','clean main')
require(len(state['completed'][1]['axiom_reports'])==13,'thirteen audits')
require('warning:' not in Path(state['completed'][1]['log']).read_text(),'no final warning')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
bundle=REV/'validator-full-seed-theory222-author-replay';require(not bundle.exists(),'new freeze path')
bundle.mkdir()
shutil.copytree(OUT/'attempts',bundle/'attempts')
for name in ['prepare','build','freeze']:
    shutil.copy2('/tmp/full-seed-theory222-'+name+'.py',bundle/(name+'.py'))
shutil.copy2('/tmp/full-seed-theory-plan.py',bundle/'plan-driver.py')
shutil.copy2('/tmp/validator-full-seed-theory222-plan-initial.json',bundle/'initial-plan.json')
shutil.copy2(OUT/'inputs.json',bundle/'inputs.json')
for r in state['completed']:shutil.copy2(r['source'],bundle/Path(r['source']).name)
for p in (D/'research').glob('validator-full-seed-theory222-plan.*'):
    shutil.copy2(p,bundle/p.name)
manifest=[]
for p in sorted(bundle.rglob('*')):
    if p.is_file():manifest.append({'path':str(p.relative_to(bundle)),'sha256':sha(p),'bytes':p.stat().st_size})
(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
attempts=[]
for a in sorted((OUT/'attempts').iterdir()):
    st=json.loads((a/'state.json').read_text())
    attempts.append({'path':str(a),'status':st['status'],'state_sha256':sha(a/'state.json'),
      'runs':[{'module':r['module'],'source_sha256':r['source_sha256'],'exit_code':r['exit_code'],
      'seconds':r['seconds'],'log_sha256':r['log_sha256']} for r in st['completed']]})
summary={'status':'PASS',
 'scope':'Concrete Delta1 recognizer of the unchanged universally closed actual full-seed body, using an exactly range-equivalent negative reparameterization and a fixed Sigma1 body graph. Genuine I-Sigma2 C222 AxOK for seedSchema and for equality plus literal membership-irreflexivity plus seedSchema, with an actual History222 value2 witness from an internal refutation. Internal closure lengths/matrices/free environments retained; no supplied axiom-image premise, raw CP/GIC, tagged quotient, source-ZFC, runtime215 or HA equation claim.',
 'inputs':data,'input_inventory_sha256':sha(cache),
 'completed':state['completed'],'final_run':str(last),'observation_count':state['observation_count'],
 'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'attempts':attempts,
 'development':'Four preserved compiler attempts: two failed mains; one clean main followed by failed Checks; final main/check pair pass. Failures were default-heartbeat quotation/monolithic-graph elaboration, local names/rewrite direction, a small Nat bound conversion, and missing Checks namespace opening. Fixed graph factored into explicit constituent graphs and fixed-quote cast lemmas; no cap increase or import change. No accepted source/dependency/Foundation objects changed or rebuilt.',
 'read_scope':'Both complete final sources, every edited proof delta, and preparation/build/freezing drivers were read before their relevant execution. SchemaClosure, source-body/typed/quote contracts, actual C222 ALL/freshness, equality and SourceDerivation contracts were read. Source-only independent challenge covered the earlier complete draft and reported no mathematical issue; it was not compiler acceptance of the final packet.'}
p=REV/'validator-full-seed-theory222-replay.json';require(not p.exists(),'new summary')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'manifest_sha256':sha(bundle/'FILES.json'),
 'files':len(manifest),'observations':state['observation_count'],
 'inherited_observations':len(data['inherited_observations']),
 'sources':[{k:r[k] for k in ['module','source_sha256','seconds','object']} for r in state['completed']]},indent=2))
