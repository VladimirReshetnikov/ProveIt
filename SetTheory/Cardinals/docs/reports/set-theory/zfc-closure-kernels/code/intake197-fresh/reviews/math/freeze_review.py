"""Own read-only provenance recorder, not a submitted mathematical checker."""
from pathlib import Path
import hashlib,json

HERE=Path(__file__).resolve().parent
P=HERE.parent/'extracted/K216_Permuted_Commands_2026-10-21'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
read_files=[
'report.tex','sections/source_calibration.tex','sections/inherited_dominated_core.tex',
'machine/local81-proof.tex','README.md','source/README.md','machine/README.md',
'secondary/README.md','provenance/ATTRIBUTION.md','provenance/source_proof_review.md',
'code/build_sources.py','code/audit_command_permutation.py','code/reconstruct.py',
'code/audit_source210.py','code/audit_blank210.py','code/build_dominated_source.py',
'machine/audit.py','verify.py']
files={str(P/r):{'sha256':sha(P/r),'lines':len((P/r).read_text().splitlines()),'role':'full source read'} for r in read_files}
for p in sorted((HERE/'dependencies').glob('*.py')):
 files[str(p)]={'sha256':sha(p),'lines':len(p.read_text().splitlines()),'role':'exact nested ancestor source, fully read; no execution'}
for p in [HERE/'dossier.md',Path('/tmp/zfc-intake197/run.py'),Path('/tmp/zfc-intake197/secondary_blank.py'),Path(__file__)]:
 files[str(p)]={'sha256':sha(p),'lines':len(p.read_text().splitlines()),'role':'own/root review or replay source read; not invoked by reviewer'}
artifacts={r:sha(P/r) for r in ['machine/k216.native.tm','machine/k216.tm','machine/sites216.json','machine/canonicalization.json','secondary/k216-120.native.tm','secondary/k216-120.tm','secondary/sites120.json','secondary/canonicalization.json','source/frozen202.json','source/reference205.json','parent/K217_Dominated_Continuation_2026-10-20.zip']}
inventory={'files':files,'artifact_pins':artifacts,'actual_member_count':sum(p.is_file() for p in P.rglob('*'))}
assert inventory['actual_member_count']==72
(HERE/'inventory.json').write_text(json.dumps(inventory,indent=2)+'\n')
review={'status':'ORDINARY_MATH_AND_SELECTED_EXECUTABLE_SOURCE_REVIEW_PASS',
 'reviewer':'drop_contract','role':'independent mathematical/code source reviewer; no candidate execution; root owns replay',
 'source':159,'package':str(P),'inventory_sha256':sha(HERE/'inventory.json'),'dossier_sha256':sha(HERE/'dossier.md'),
 'scope':['complete main manuscript and proof appendices','raw numerical compiler including I(0,0) alias and exact stack reset','cofinal enumeration from cutoff4','literal local81 whole-tape lemma','selected new executable closure and exact inherited runtime files','review of root ten-leaf runner and independent secondary blank driver'],
 'findings':[],
 'documentation_caveats':['source/README lists absent standalone documents, audit files, rebuilt output and scripts with historical locations; recovery contains actual72 members only'],
 'fresh_results':'pending root review at freeze; this receipt makes no actual pass claim',
 'excluded':['submitted execution','ancestor proof-suite replay','manifest verification','C++ compilation','Lean or Rocq endpoint','transitive historical proof recheck','minimality or <=215 claim']}
(HERE/'review.json').write_text(json.dumps(review,indent=2)+'\n')
print(json.dumps({'review_sha256':sha(HERE/'review.json'),'inventory_sha256':sha(HERE/'inventory.json'),'dossier_sha256':sha(HERE/'dossier.md'),'reviewed_files':len(files)}))
