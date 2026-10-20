"""Own bounded note/evidence bindings, after full ordinary prose review; no supplied execution."""
from pathlib import Path
import re,json,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');H=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels';O=Path('/tmp/zfc-catalogue189-190')
def d(p):return {'path':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
notes=[H/f'intake-{n}{s}.md'for n in(189,190)for s in('','-reproduction')];links=[]
for p in notes:
 text=p.read_text();text=re.sub(r'```.*?```|`[^`]*`','',text,flags=re.S)
 for m in re.finditer(r'\[[^\]]*\]\(([^)]+)\)',text):
  target=m[1].split('#')[0]
  if not target or '://' in target:continue
  assert (p.parent/target).exists(),(p,target);links.append({'source':str(p.relative_to(R)),'target':target})
assert 'unions\nof different restricted rows' not in notes[0].read_text()
a145=H/'data/intake189-fresh-state-search/actual.json';a147=H/'data/intake190-fresh-k218/execution/result.json'
for p,n in [(a145,5),(a147,6)]:
 j=json.loads(p.read_text());assert j['status']=='FRESH_DIRECT_LEAVES_PASS' and j['inputs_unchanged'] and len(j['jobs'])==n
 assert all(x['returncode']==0 and not x['timed_out'] and x['inputs_unchanged'] for x in j['jobs'])
runtime=H/'data/intake190-fresh-k218/execution/output/runtime/runtime.json';j=json.loads(runtime.read_text());assert j['cases']==6167 and j['symbolic_steps']==1514325 and not j['failures'] and j['generic_cases_excluded']==0
recover=[H/f'data/intake{n}-recovery.json' for n in(189,190)];assert [sum(x['members']for x in json.loads(p.read_text()))for p in recover]==[1036,102]
record={'status':'INDEPENDENT_INTAKE_NOTE_REVIEW_PASS','reviewer':'review_upstream_reflection','findings':[],'notes':[d(p)for p in notes],'bound_evidence':[d(p)for p in [a145,a147,runtime,*recover,H/'data/intake189-source-review.json',H/'data/intake190-source-review.json',H/'intake190-membership-extension.md']],'reviewer_source':d(Path(__file__)),'local_links_checked':links,'mathematical_review':['Both source145/146 main manuscripts and substantive supplements were read in the frozen earlier independent review; final189 note preserves T-only versus T+EXP scope, code-level versus physical/runtime claims, fixed-label full-vacuity premises, clean-seed/frame hypotheses and fixed-power-of-two scheduler limits.','Source145 five fresh jobs are distinct from source146 delivered runtime and own fresh literal/startup/ray checks. The initialized218 blank failure is not a consistency machine.','Source147 ordinary exact-CFG and contextual preceding-bit decoder proof, complete frame/runtime/startup and inherited calibration remain distinct. Same two folded subtree roles prevent double-counting the savings. Primary218 remains primary; no217 or exact-table kernel endpoint follows.','Five-value numerical derivability model covers all membership fourth inputs jointly. The ordinary PA-formalizable induction and independent finite diagnostic are not reported as new Lean/Rocq proofs or ordinary set-theoretic models. K/EFQ remain outside the obstruction.'],'resolved_findings':['190 actual/review links corrected to execution/result.json and review/review.json in both files.','Final source147 fold described as decoder sharing and contextual reassociation.','189 outer-head paragraph no longer incorrectly excludes unions within its uniformly validated family.'],'limits':['No candidate checker, simulator, search or proof assistant run by this reviewer.','Bounded actual-record checks accompany prior full source/prose review; no duplicate complete runtime or provider re-audit.','Recovery receipts read as existing root evidence; independent placement-tree audit separately checks every arrival member and exact retained Git aliases.']}
p=O/'final-note-review.json';p.write_text(json.dumps(record,indent=2)+'\n');print(p,hashlib.sha256(p.read_bytes()).hexdigest(),len(links),'links')
