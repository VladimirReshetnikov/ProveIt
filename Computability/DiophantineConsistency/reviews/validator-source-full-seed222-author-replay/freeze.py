import hashlib,json,shutil
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
D=ROOT/'Computability/DiophantineConsistency'
REV=D/'reviews'
OUT=Path('/tmp/validator-source-full-seed222-author-m7w5l6ru')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
last=Path((OUT/'latest-run').read_text().strip())
state=json.loads((last/'state.json').read_text())
require(state['status']=='PASS' and len(state['completed'])==2,'final pair')
data=json.loads((OUT/'inputs.json').read_text())
require(sha(REV/'validator-source-full-seed222-cache.json')=='83c4a8f969e6b54d06bc1db7c77541a5b367b6672a2cefd25db92c9bf7022f39','frozen cache')
for r in json.loads((last/'pins.json').read_text())+data['inherited_observations']:
    require(sha(r['path'])==r['sha256'],'final observation '+r['path'])
for r in state['completed']:
    for p,h in [(r['source'],r['source_sha256']),(r['snapshot'],r['snapshot_sha256']),
      (r['object']['path'],r['object']['sha256']),(r['log'],r['log_sha256']),
      (r['timing'],r['timing_sha256'])]:require(sha(p)==h,'final artifact '+p)
    require(not Path(r['object']['path']).is_symlink(),'regular new object')
require(Path(state['completed'][0]['log']).read_text()=='','clean main')
require(len(state['completed'][1]['axiom_reports'])==17,'seventeen audits')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
bundle=REV/'validator-source-full-seed222-author-replay';require(not bundle.exists(),'freeze path')
bundle.mkdir()
shutil.copytree(OUT/'attempts',bundle/'attempts')
for name in ['prepare','build','freeze']:
    shutil.copy2('/tmp/source-full-seed222-'+name+'.py',bundle/(name+'.py'))
for name in ['full-seed222-source-audit.py','full-seed222-source-audit-v1.py','full-seed222-source-audit-v1.log']:
    shutil.copy2('/tmp/'+name,bundle/name)
shutil.copy2(OUT/'inputs.json',bundle/'inputs.json')
for r in state['completed']:shutil.copy2(r['source'],bundle/Path(r['source']).name)
for p in (D/'research').glob('validator-source-full-seed222-plan.*'):
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
 'scope':'Actual C222 full clos-and-req seed image for every internal IsSemiformula set-language 2 p, arbitrary free environment F and StreamFree requested s, with an explicit ArithmeticHistory222.value witness. Exact meta/typed/raw source body, five substitutions, source implication encoding, matrix congruence through actual Eind and complete-stack fresh alpha intermediaries; no given source image, raw CP/GIC, tagged interpretation, full schema recognizer, source-ZFC or HA equation theorem.',
 'inputs':data,'input_inventory_sha256':sha(REV/'validator-source-full-seed222-cache.json'),
 'completed':state['completed'],'final_run':str(last),'observation_count':state['observation_count'],
 'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'attempts':attempts,
 'development':'Twelve preserved compiler attempts: nine failed, two intermediate main-only passes, final main/check pair pass. Failures concern local typed notation/quote equality/casts/API names, fixed literal quote expansion hitting the default heartbeat cap, and one Checks namespace omission. Fixed the heartbeat issue by proving and rewriting the exact seedSubset quotation separately; no cap was raised. The failed Checks error-recovery sorryAx reports were rejected with exit1 and no accepted object. Earlier source-audit metadata TypeError and its correction are also preserved separately; no compiler was involved. No frozen prerequisite was edited, and no dependency/Foundation build was run.',
 'read_scope':'Both complete final sources, the preparation/build/freezing drivers, exact selected closure headers and inherited pin records were read before the relevant execution. Final main full self-read precedes final pair; only unused private helper deletion followed that read, and its exact delta was read before execution.'}
p=REV/'validator-source-full-seed222-replay.json';require(not p.exists(),'summary freeze')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'manifest_sha256':sha(bundle/'FILES.json'),
 'files':len(manifest),'observations':state['observation_count'],
 'inherited_observations':len(data['inherited_observations']),
 'sources':[{k:r[k] for k in ['module','source_sha256','seconds','object']} for r in state['completed']]},indent=2))
