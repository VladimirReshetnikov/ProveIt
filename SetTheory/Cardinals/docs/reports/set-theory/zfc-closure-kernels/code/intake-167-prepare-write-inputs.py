"""Own static input-map writer. Does not invoke staging, supplied code, or proofs."""
from pathlib import Path
import hashlib,json,ast,subprocess,difflib
W=Path(__file__).resolve().parent; V=W/'write-v3'; R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
H='SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
Q=Path('/tmp/zfc244-rotation-root-replay'); A=Path('/tmp/zfc244-rotation-aux-replay'); C=Path('/tmp/zfc243-root-replay')
M=W.parent/'independent-math-review'
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def desc(p): return {'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
def write(p,d):
 with Path(p).open('x') as f:f.write(json.dumps(d,indent=2)+'\n')
files=[]; targets=set()
def add(src,target,role='Existing source/evidence; invocation scope remains in the record',before=None):
 src=Path(src);assert src.is_file() and target not in targets,target
 row={'source':str(src),'target':target,'sha256':sha(src),'bytes':src.stat().st_size,'role':role}
 if before is not None:row['replace_before_sha256']=before
 else:assert not (R/target).exists(),target
 files.append(row);targets.add(target)
def data(src,name,role='Immutable actual evidence, source review or history; not a new execution'):
 add(src,H+'/data/intake-167-'+name,role)
def code(src,name):add(src,H+'/code/'+name,'Exact own author/root/reviewer source; no invocation by the write helper')
placement=json.loads((W/'placement-proposal.json').read_text()); placed={r['sha256']:r for r in placement['files'] if r['disposition']=='place_unchanged'}
before=sha(R/H/'README.md');assert before==json.loads((W/'write-draft-status.json').read_text())['host_before_sha256']
add(V/'host-README.md',H+'/README.md','Only maintained-file replacement: source71 host reconciliation/count/current baseline',before)
for n in ['intake-167.md','intake-167-reproduction.md','intake-167-source-71.md']:add(V/n,H+'/'+n,'Final authored reconciliation/reproduction/full source dossier')
add(W/'auxiliary-replay-plan.md',H+'/intake-167-auxiliary-replay-plan.md','Portable command/dependency/cost table; actual outcomes separately reviewed')
for src,n in [(W/'recover_167.py','recover_167.py'),(W/'place_167.py','intake-167-place.py'),(W/'write_167.py','intake-167-write-helper.py'),(Path(__file__),'intake-167-prepare-write-inputs.py'),(W.parent/'inventory_intake.py','intake-167-inventory.py'),(W/'prepare_placement.py','intake-167-prepare-placement.py'),(W/'prepare_auxiliary_plan.py','intake-167-prepare-auxiliary-plan.py'),(W/'review_primary_replay.py','intake-167-review-primary.py'),(W/'review_auxiliary_replay.py','intake-167-review-auxiliary.py'),(Q/'replay.py','intake-167-root-primary-replay.py'),(A/'runner.py','intake-167-root-auxiliary-replay.py'),(M/'review_static.py','intake-167-review-ordinary.py'),(C/'independent-review/review_quick.py','intake-167-review-combined243-quick.py'),(C/'independent-review/review_expanded.py','intake-167-review-combined243-expanded.py'),(W/'finalize_write_drafts.py','intake-167-finalize-write-v2.py'),(W/'finalize_write_v3.py','intake-167-finalize-write-v3.py')]:code(src,n)
for src,n in [('placement-proposal.json','placement.json'),('inventory.json','inventory.json'),('find-object-output.txt','history-find-object.txt'),('find-object-stderr.txt','history-find-object-stderr.txt'),('backend-reuse.json','backend-reuse.json'),('primary-replay-review.json','primary-review.json'),('auxiliary-replay-review.json','auxiliary-review.json'),('auxiliary-replay-plan.json','auxiliary-replay-plan.json'),('placement-helper-source-plan.json','placement-helper-source-plan.json'),('write-draft-status.json','write-v2-status.json'),('write-v3-freeze.json','write-v3-freeze.json')]:data(W/src,n)
for name in ['placement.json','stage-paths.txt','retire-paths.txt','commit-message.txt']:data(Path('/tmp/zfc-intake-167-placement')/name,'root-'+name)
data(Path('/tmp/zfc-intake-167-recovery-check/recovery.json'),'recovery.json')
for version in ['write-v1','write-v2']:
 for f in sorted((W/version).iterdir()):
  if f.is_file():data(f,'history-'+version+'-'+f.name,'Preserved earlier uninstalled prose/diff; selected write-v3 supersedes it')
for f in sorted(V.glob('*.diff')):data(f,'write-v3-'+f.name)
for f in sorted((W/'history').rglob('*')):
 if f.is_file():data(f,'planning-history-'+str(f.relative_to(W/'history')).replace('/','-'))
for f,n in [('review.json','ordinary-review.json'),('review.md','ordinary-review.md'),('static-comparison.json','ordinary-static-comparison.json')]:data(M/f,n)
for f in sorted((M/'history').rglob('*')):
 if f.is_file():data(f,'ordinary-history-'+str(f.relative_to(M/'history')).replace('/','-'))
for f,n in [('execution.json','primary-execution.json'),('verification.json','primary-verification.json'),('built/expanded-runtime.json','expanded-runtime.json'),('built/affine-runtime.json','affine-runtime.json'),('built/literal-regression.json','literal-regression.json'),('built/literal-regression-cases.json.gz','literal-regression-cases.json.gz'),('frames.json','frames.json'),('blank/independent-blank.json','independent-blank.json'),('source/source_verification.json','source-verification.json'),('source/left/source_verification.json','source-left-verification.json'),('source/right/source_verification.json','source-right-verification.json')]:data(Q/'run1'/f,n)
for f in sorted((Q/'run1').glob('*.log')):data(f,'primary-'+f.name+'.txt')
data(Q/'inherited-identity.json','inherited-identity.json')
for f in sorted((Q/'auxiliary').iterdir()):
 if f.is_file():data(f,'auxiliary-'+f.name+('.txt' if f.suffix=='.log' else ''))
data(A/'verification.json','auxiliary-execution.json')
for f in sorted(A.glob('*.log')):data(f,'auxiliary-'+f.name+'.txt')
# New substantive outputs are retained; three large exact regenerated families reuse placed bytes.
aliases=[]
aux=json.loads((W/'auxiliary-replay-review.json').read_text())
for rec in aux['new_outputs']:
 p=Path(rec['path']);assert sha(p)==rec['sha256']
 if rec['sha256'] in placed:
  dest=placed[rec['sha256']]['target'];assert sha(R/dest)==rec['sha256'];disposition='Exact existing placed payload; no duplicate copy'
 else:
  dest=H+'/data/intake-167-fresh-'+p.name;add(p,dest);disposition='New substantive generated output retained'
 aliases.append(dict(rec,maintained_target=dest,disposition=disposition))
# Map other exact root result files to delivered payloads where possible, preserving absolute evidence names.
for p in sorted((Q/'run1').rglob('*')):
 if p.is_file() and sha(p) in placed:aliases.append(dict(desc(p),maintained_target=placed[sha(p)]['target'],disposition='Exact placed bytes also produced by the primary replay'))
write(W/'fresh-output-map.json',{'status':'EXACT_REPLAY_OUTPUT_PATH_MAP','aliases':aliases,'scope':'No regenerated file overwrites delivery; record paths remain historical. All comparisons are byte identity.'})
data(W/'fresh-output-map.json','fresh-output-map.json')
for f,n in [('quick-verification.json','combined243-quick-verification.json'),('expanded-verification.json','combined243-expanded-verification.json'),('expanded-execution.json','combined243-expanded-execution.json'),('candidate/expanded-runtime.json','combined243-expanded-runtime.json'),('independent-review/expanded-review.json','combined243-expanded-review.json'),('independent-review/quick-review.json','combined243-quick-review.json')]:data(C/f,n)
for f in sorted(C.glob('*.log')):data(f,'combined243-'+f.name+'.txt')
# Candidate sources/adapters/ordinary proof are already durable in c7069ecd39; no duplication.
archive=R/'docs/incoming/zfc-raw-profile-routing-20261018.zip'
arrival=subprocess.check_output(['git','rev-parse','1590329560'],cwd=R,text=True).strip()
blob=subprocess.check_output(['git','rev-parse',arrival+':docs/incoming/zfc-raw-profile-routing-20261018.zip'],cwd=R,text=True).strip()
pending=sorted(str(p.relative_to(R)) for p in (R/'docs/incoming').glob('*.zip'));assert len(pending)==19
write(W/'queue-supplement.json',{'status':'SEPARATE_LATER_QUEUE_ARRIVAL','placement_pending_count':18,'arrival':arrival,'archive':str(archive.relative_to(R)),'git_blob':blob,'sha256':sha(archive),'bytes':archive.stat().st_size,'current_pending_count':len(pending),'pending_paths':pending,'scope':'Not part of batch167; original inventory and placement map unchanged.'})
data(W/'queue-supplement.json','queue-supplement.json')
records={'primary':Q/'run1/verification.json','expanded':Q/'run1/built/expanded-runtime.json','primary_review':W/'primary-replay-review.json','auxiliary':A/'verification.json','logical':Q/'auxiliary/logical-execution.json','auxiliary_review':W/'auxiliary-replay-review.json','combined':C/'expanded-verification.json','combined_review':C/'independent-review/expanded-review.json','recovery':Path('/tmp/zfc-intake-167-recovery-check/recovery.json')}
for p in records.values():assert any(r['source']==str(p) for r in files),p
fullplacement=subprocess.check_output(['git','rev-parse','5513e77ff1'],cwd=R,text=True).strip()
manifest={'status':'READY_FOR_ROOT_SOURCE_REVIEW','batch':167,'host_source':71,'collection_reports':290,'placement':fullplacement,'candidate_publication':'c7069ecd39','relative_lean_publication':'8778a52515','base_article':{'path':H+'/article.tex','sha256':sha(R/H/'article.tex')},'placement_map':desc(W/'placement-proposal.json'),'records':{k:desc(v) for k,v in records.items()},'files':files,'status_boundaries':['Incoming ordinary source proof and actual seven-job primary replay; sixteen auxiliary jobs separately reviewed.','Combined243 is a subsequent derivation with complete Python replay and relative Lean comparison only; no complete243 consistency or PA endpoint.','Only host README replaced; delivered inputs/article/PDF unchanged. Root owns separate catalogue manifest/PDF update.','v1/v2 prose, ordinary reviewer correction and all available job/log evidence retained.','Historical eighteen-archive placement queue and later nineteenth arrival kept distinct.'],'builder_execution':'Not invoked; root alone stages/installs/commits.'}
ast.parse((W/'write_167.py').read_text());write(W/'write-inputs.json',manifest)
print(json.dumps({'files':len(files),'with_manifest':len(files)+1,'bytes':sum(x['bytes'] for x in files),'inputs_sha256':sha(W/'write-inputs.json'),'helper_sha256':sha(W/'write_167.py'),'host_before_sha256':before},indent=2))
