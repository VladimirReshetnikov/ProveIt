import hashlib,json,shutil
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=ROOT/'Computability/DiophantineConsistency/reviews'
OUT=Path('/tmp/validator-proof-context222-author-b4vpgdet')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
    if not c:raise RuntimeError(m)
last=Path((OUT/'latest-run').read_text().strip());state=json.loads((last/'state.json').read_text())
require(state['status']=='PASS' and len(state['completed'])==2,'final pair')
data=json.loads((OUT/'inputs.json').read_text())
for r in state['completed']:
    require(sha(r['source'])==r['source_sha256'],'final source')
    require(sha(r['object']['path'])==r['object']['sha256'],'final object')
    require(sha(r['log'])==r['log_sha256'],'final log')
require(Path(state['completed'][0]['log']).read_text()=='','clean main')
require(len(state['completed'][1]['axiom_reports'])==16,'sixteen audits')
bundle=REV/'validator-proof-context222-author-replay';require(not bundle.exists(),'freeze path')
bundle.mkdir()
shutil.copytree(OUT/'attempts',bundle/'attempts')
for name in ['prepare','build','freeze']:shutil.copy2('/tmp/proof-context222-'+name+'.py',bundle/(name+'.py'))
shutil.copy2(OUT/'inputs.json',bundle/'inputs.json')
for r in state['completed']:shutil.copy2(r['source'],bundle/Path(r['source']).name)
manifest=[]
for p in sorted(bundle.rglob('*')):
    if p.is_file():manifest.append({'path':str(p.relative_to(bundle)),'sha256':sha(p),'bytes':p.stat().st_size})
(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary={'status':'PASS','scope':'Actual C222 internal context calculus, fixed fold graphs and enumeration transport under IΣ1; no source-axiom image or complete proof interpretation.',
 'inputs':data,'input_inventory_sha256':sha(REV/'validator-proof-context222-cache.json'),
 'completed':state['completed'],'final_run':str(last),'observation_count':state['observation_count'],
 'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'development':'Unexecuted overstrong false-sequent check corrected during self-read; first main failed only explicit Enum graph hierarchy elaboration; second pair passed with one unused-binder warning; final pair passed without warnings. All sources/logs/plans/driver snapshots and previous successful objects retained.',
 'guide':{'path':str(ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Ctx.lean'),'sha256':sha(ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Ctx.lean'),'role':'read/adaptation guide only; not imported'}}
p=REV/'validator-proof-context222-replay.json';require(not p.exists(),'summary freeze')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'manifest_sha256':sha(bundle/'FILES.json'),'files':len(manifest),'observations':state['observation_count'],'sources':[{k:r[k] for k in ['module','source_sha256','seconds','object']} for r in state['completed']]},indent=2))
