import hashlib,json,shutil
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=ROOT/'Computability/DiophantineConsistency/reviews'
OUT=Path('/tmp/validator-source-quantifier-context222-author-up2sx7d8')
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
require(len(state['completed'][1]['axiom_reports'])==23,'twenty-three audits')
bundle=REV/'validator-source-quantifier-context222-author-replay';require(not bundle.exists(),'freeze path')
bundle.mkdir()
shutil.copytree(OUT/'attempts',bundle/'attempts')
for name in ['prepare','build','freeze']:shutil.copy2('/tmp/source-quantifier-context222-'+name+'.py',bundle/(name+'.py'))
shutil.copy2(OUT/'inputs.json',bundle/'inputs.json')
for r in state['completed']:shutil.copy2(r['source'],bundle/Path(r['source']).name)
for p in Path('/tmp').glob('source-quantifier-context222-plan*.py'):
    shutil.copy2(p,bundle/p.name)
for p in Path('/tmp').glob('source-quantifier-context222-plan*-failure.txt'):
    shutil.copy2(p,bundle/p.name)
for p in (ROOT/'Computability/DiophantineConsistency/research').glob('validator-source-quantifier-context222-plan.*'):
    shutil.copy2(p,bundle/p.name)
manifest=[]
for p in sorted(bundle.rglob('*')):
    if p.is_file():manifest.append({'path':str(p.relative_to(bundle)),'sha256':sha(p),'bytes':p.stat().st_size})
(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary={'status':'PASS','scope':'Actual C222 generalization through internal vacuous contexts and typed encoded source contexts, literal shifted/opened ALL and arbitrary-context EXS term rules, sequent rules and actual-history witnesses. Explicit ISigma2; no source-axiom images or full interpreter.',
 'inputs':data,'input_inventory_sha256':sha(REV/'validator-source-quantifier-context222-cache.json'),
 'completed':state['completed'],'final_run':str(last),'observation_count':state['observation_count'],
 'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'development':'First main attempt failed only because a doc comment preceded omit rather than the theorem. Moved omit before the comment without changing any theorem. Next pair passed with 22 audits. Added the planned two-source-shift check, replacing a redundant wrapper; final pair passed with 23 audits, empty main and no warnings. All attempts, sources, logs, pins and previous successful objects retained.',
 'guide':{'path':str(ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Quant.lean'),'sha256':sha(ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Quant.lean'),'role':'read/adaptation guide only; not imported'}}
p=REV/'validator-source-quantifier-context222-replay.json';require(not p.exists(),'summary freeze')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'manifest_sha256':sha(bundle/'FILES.json'),'files':len(manifest),'observations':state['observation_count'],'sources':[{k:r[k] for k in ['module','source_sha256','seconds','object']} for r in state['completed']]},indent=2))
