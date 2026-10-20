"""Publish only owned new evidence/code files after the actual review passes."""
from pathlib import Path
import hashlib,json,shutil
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs');H=ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
E=Path('/tmp/zfc-intake187/opening-execution');R=Path(__file__).resolve().parent
C=H/'code/intake187-fresh-alternatives';D=H/'data/intake187-fresh-alternatives'
assert not C.exists() and not D.exists();C.mkdir(parents=True);D.mkdir(parents=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert json.loads((R/'review.json').read_text())['status']=='FRESH_SOURCE141_DIRECT_LEAF_REPLAY_REVIEW_PASS'
files=[]
def cp(src,dst):
 src=Path(src);dst.parent.mkdir(parents=True,exist_ok=True);assert not dst.exists();shutil.copy2(src,dst);assert src.read_bytes()==dst.read_bytes();files.append({'target':str(dst.relative_to(ROOT)),'source':str(src),'sha256':sha(dst),'bytes':dst.stat().st_size})
for n in ('prepare_replay.py','run_replay.py','prepare-portable.diff','run-portable.diff'):cp(R/n,C/n)
for n in ('prepare.py','run.py','finalize_review.py','publish.py'):cp(R/n,C/'actual-adapter'/n)
for folder,names in [('portable',('construct.py','check_source.py','check_runtime.py','canonicalize.py','reproduce.py')),('verification',('independent_source_check.py','independent_small_audit.py','independent_runtime_audit.py','negative_controls.py'))]:
 for n in names:cp(E/'packet'/folder/n,C/'supplied'/folder/n)
for n in ('symbolic_runtime.py','independent_runtime.py'):cp(E/'runtime-vendor'/n,C/'supplied/runtime-vendor'/n)
for src,name in [(E/'result.json','actual.json'),(E/'plan.json','plan.json'),(E/'legacy_mapping.json','inputs/legacy_mapping.json'),(E/'packet/machine/construction.json','inputs/construction.json'),(R/'review.json','review.json'),(R/'notes.md','source-review.md'),(R/'runtime-input-lineage.json','runtime-input-lineage.json'),(R/'portable-review.json','portable-review.json'),(Path('/tmp/zfc-intake187/opening-portable-prepared/plan.json'),'portable-prepared-plan.json'),(Path('/tmp/zfc-intake187-opening-reproduction.md'),'reproduction.md')]:cp(src,D/name)
for folder in ('logs','output'):
 for p in sorted((E/folder).rglob('*')):
  if p.is_file():cp(p,D/folder/p.relative_to(E/folder))
record={'status':'OWNED_EVIDENCE_COPY_PASS','scope':'Exact new host copies of the completed14-job direct replay, own review and portable adapter. Original supplied payload and core candidate unchanged. Historical absolute scratch paths retained in actual records.','files':files}
q=D/'publication.json';q.write_text(json.dumps(record,indent=2)+'\n')
owned=[x['target']for x in files]+[str(q.relative_to(ROOT))]
(R/'owned-files.json').write_text(json.dumps(owned,indent=2)+'\n')
print(json.dumps({'files':len(owned),'publication_sha256':sha(q),'total_bytes':sum(x['bytes']for x in files)},indent=2))
