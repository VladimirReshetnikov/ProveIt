import hashlib,json,shutil
from pathlib import Path
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
REV=ROOT/'Computability/DiophantineConsistency/reviews'
OUT=Path('/tmp/validator-source-derivation222-author-wzu97kmp')
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
require(len(state['completed'][1]['axiom_reports'])==17,'seventeen audits')
bundle=REV/'validator-source-derivation222-author-replay';require(not bundle.exists(),'freeze path')
bundle.mkdir()
shutil.copytree(OUT/'attempts',bundle/'attempts')
for name in ['prepare','build','freeze']:shutil.copy2('/tmp/source-derivation222-'+name+'.py',bundle/(name+'.py'))
shutil.copy2(OUT/'inputs.json',bundle/'inputs.json')
for r in state['completed']:shutil.copy2(r['source'],bundle/Path(r['source']).name)
for p in Path('/tmp').glob('source-derivation222-plan*.py'):
    shutil.copy2(p,bundle/p.name)
for p in Path('/tmp').glob('source-derivation222-plan*-failure.txt'):
    shutil.copy2(p,bundle/p.name)
for p in (ROOT/'Computability/DiophantineConsistency/research').glob('validator-source-derivation222-plan.*'):
    shutil.copy2(p,bundle/p.name)
manifest=[]
for p in sorted(bundle.rglob('*')):
    if p.is_file():manifest.append({'path':str(p.relative_to(bundle)),'sha256':sha(p),'bytes':p.stat().st_size})
(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n')
summary={'status':'PASS','scope':'Actual ten-case internal Foundation proof interpretation into C222, explicit Pi2/ISigma2 induction, typed arbitrary environments and contexts with StreamFree, modular AxOK theory-image boundary, actual value2 refutation witness. No concrete source axiom images, closed ZFC reduction or HA equation equivalence.',
 'inputs':data,'input_inventory_sha256':sha(REV/'validator-source-derivation222-cache.json'),
 'completed':state['completed'],'final_run':str(last),'observation_count':state['observation_count'],
 'bundle':str(bundle),'manifest_sha256':sha(bundle/'FILES.json'),
 'development':'Five preserved attempts. First main failed on tail namespace, graph-instance projection and definability search, plus final CProv unfolding. Second revealed broad old/new encoder name ambiguity and the recursive definability search; narrowed tail import and replaced search with explicit accepted graph composition. Third main checked all ten cases but needed the explicit internal one_add_one_eq_two rewrite in the final witness. Fourth main passed; duplicate-enumeration check needed actual membership equivalence rather than unregistered numeric insert-idempotence simp. Fifth final pair passed cleanly with 17 standard-only audits. Failed logs include the diagnostic sorryAx of a failed check; no successful object/report contains it. All attempts, source snapshots, drivers, pins, timings, logs and previous successful main object are retained.',
 'guide':{'path':str(ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Main.lean'),'sha256':sha(ROOT/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/R2Main.lean'),'role':'fully read source/adaptation guide only; not imported'}}
p=REV/'validator-source-derivation222-replay.json';require(not p.exists(),'summary freeze')
p.write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'summary':str(p),'summary_sha256':sha(p),'manifest_sha256':sha(bundle/'FILES.json'),'files':len(manifest),'observations':state['observation_count'],'sources':[{k:r[k] for k in ['module','source_sha256','seconds','object']} for r in state['completed']]},indent=2))
