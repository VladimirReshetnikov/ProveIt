"""Own scratch-only copy map for batch165; executes no supplied code and copies no repo files."""
from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');W=Path('/tmp/zfc-intake-165-planning');O=W/'write-final';H=Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels');rows=[]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def add(src,target,role):
 src=Path(src);src=src if src.is_absolute() else W/src;dest=H/target
 assert src.is_file() and not src.is_symlink(),src
 assert not (R/dest).exists(),dest
 assert str(dest) not in {r['target'] for r in rows}
 assert len('C:\\ProveIt\\'+str(dest).replace('/','\\'))<200,(dest,len(str(dest)))
 rows.append({'source':str(src),'target':str(dest),'sha256':sha(src),'bytes':src.stat().st_size,'role':role})
for n in ['intake-165.md','intake-165-reproduction.md']:add(O/n,n,'final reconciliation/reproduction')
add('source69-dossier.md','intake-165-source-69.md','immutable historical source dossier; supplemental status was pending at its freeze')
for n in ['recover_165.py','place_165.py','inventory_archives.py','history_matches.py','freeze_plan.py','supplement_queue.py','review_main_replay.py','review_supplemental_replay.py','prepare_write.py','prepare_publication_map.py','run_source69_main.py','run_source69_supplemental.py']:
 target=n if n=='recover_165.py' else 'intake_165_'+n
 add(n,'code/'+target,'recovery helper or exact author/root-executed historical static/replay source; no new execution')
for src,suffix in [
 ('placement-proposal.json','placement.json'),('inventory.json','historical-inventory.json'),('history-matches.json','history-matches.json'),('find-object-raw.txt','history-output.txt'),('find-object-stderr.txt','history-stderr.txt'),('queue.json','historical-queue.json'),('queue-supplement/queue-supplement.json','queue-supplement.json'),('execution-plan.json','execution-plan.json'),('source69-main-replay-review.json','source69-main-review.json'),('source69-supplemental-replay-review.json','source69-supplemental-review.json'),('/tmp/zfc-intake-165-placement/placement.json','placement-execution.json'),('/tmp/zfc-intake-165-placement/staged-review.json','staged-review.json'),('/tmp/zfc-intake-165-placement/commit-message.txt','placement-commit-message.txt'),('/tmp/zfc-intake-165-recovery-check/recovery.json','recovery.json'),('write-final/readiness.json','write-readiness.json')]:
 add(src,'data/intake-165-'+suffix,'immutable intake/history/placement/recovery/review evidence; proposal status retained separately from actual placement')
main=Path('/tmp/zfc-intake-165-source69-main-run1');M=json.loads((main/'execution.json').read_text());assert M['status']=='PASS' and len(M['summary']['jobs'])==14
add(main/'execution.json','data/intake-165-source69-main-execution.json','root actual main execution')
for channel in ['stdout','stderr']:add(M[channel],f'data/intake-165-source69-main-{channel}.txt','root raw main stream')
for j in M['summary']['jobs']:
 p=main/'package/results'/(j['name']+'.log')
 if p.exists():add(p,f'data/intake-165-source69-main-{j["name"]}.txt','root regenerated child combined stream')
mainouts=['code/source-exactroot-affine-verification.json','results/source-invariant-affine-verification.json','results/invariants-rechecked.json','results/quiet-blocks-rechecked.json','results/relaxed-affine-controls.json','results/arithmetic-block-controls.json','results/rejected-table-check.json','results/union-graph-certificates.json','results/threshold-literal-witness.json','results/verification-summary.json']
for i,n in enumerate(mainouts):add(main/'package'/n,f'data/intake-165-source69-main-output{i:02d}.json','root regenerated semantic output; original member path retained here')
supp=Path('/tmp/zfc-intake-165-source69-supplemental-run1');S=json.loads((supp/'execution.json').read_text());assert S['status']=='PASS' and len(S['records'])==8
add(supp/'execution.json','data/intake-165-source69-supplemental-execution.json','root actual eight supplemental executions')
for i,j in enumerate(S['records'],1):
 assert j['status']=='PASS' and j['exit_code']==0 and not j['timed_out']
 for channel in ['stdout','stderr']:add(j[channel],f'data/intake-165-source69-supp{i:02d}-{channel}.txt','root raw supplemental stream')
 add(supp/j['key']/'execution.json',f'data/intake-165-source69-supp{i:02d}-execution.json','root per-attempt record')
outputs=[('reference-literal-instructions','results/literal-instructions.json'),('reference-local-contracts','results/literal-local-contracts.json'),('reference-prefix-boxes','results/prefix-box-regression.json'),('reference-independent-audit','reviews/audit246-results.json'),('reference-independent-rebuild','review-rebuilt246/zfc_fold246_old.tm'),('reference-independent-rebuild','review-rebuilt246/zfc_fold246.tm'),('reference-independent-rebuild','review-rebuilt246/independent-bootstrap-audit.json'),('reference-independent-rebuild','review-rebuilt246/renumbering-and-table-audit.json')]
for i,(key,n) in enumerate(outputs):
 p=supp/key/'package/reference/context246'/n
 add(p,f'data/intake-165-source69-supp-output{i:02d}{p.suffix}','root regenerated reference output; original source path retained here')
add(supp/'emitter-baseline/package/results/recomputed-emitter-baseline.json','data/intake-165-source69-emitter-baseline.json','root regenerated203/246/8391/empty-failures baseline')
targets={r['target'] for r in rows};links=[]
for p in [O/'intake-165.md',O/'intake-165-reproduction.md',O/'README.md']:
 for l in re.findall(r'\]\(([^)]+)\)',p.read_text()):
  if '://' in l or l.startswith('#'):continue
  l=l.split('#')[0];dest=(R/H/l).resolve();assert str(dest).startswith(str(R)+'/')
  assert str(dest.relative_to(R)) in targets or dest.exists(),(p,l)
  links.append({'document':p.name,'link':l,'target':str(dest.relative_to(R))})
record={'status':'READY_FOR_ROOT_REVIEW_AND_COPY','batch':165,'placement':'500381f8f1b4f450870895a642a2845a15a008ea','host_sources':69,'collection_reports':290,'files':rows,'total_files':len(rows),'total_bytes':sum(r['bytes'] for r in rows),'link_checks':links,'host_readme_replacement':{'source':str(O/'README.md'),'target':str(H/'README.md'),'before_sha256':'6604d42ebfa83c4e1ccb0d39f78cc1b6ce5785f8c1d21770005eb88ea6579dbb','sha256':sha(O/'README.md'),'patch':str(O/'host-readme.patch')},'fresh_checks':{'main_named_jobs':14,'supplemental_jobs':8,'optional_searches_replayed':False,'proof_or_TeX_builds':False},'scope':['The historical placement proposal and source dossier retain their original status; actual commit/staged/recovery records govern completion.','Historical raw execution paths are preserved; this map binds their published counterparts.','All delivered files and the base article remain unchanged.','Catalogue write/PDF build and independent write review are separate; no reviewed theorem gains formal status by intake.']}
(O/'publication-map.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps({'files':len(rows),'bytes':record['total_bytes'],'links':len(links),'map_sha256':sha(O/'publication-map.json')},indent=2))
