from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path(__file__).resolve().parent
H=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels';C=R/'Computability/BusyBeaver/Research/ZFC/candidate-k217/presentations/exposed-marker'
def d(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
notes=[H/'intake-194.md',H/'intake-194-reproduction.md',C/'README.md'];links=[]
for p in notes:
 for target in re.findall(r'\]\(([^)\s]+)\)',p.read_text()):
  if '://'in target or target.startswith('#'):continue
  q=(p.parent/target.split('#')[0]).resolve();assert q.exists(),(str(p),target)
  links.append({'from':str(p),'target':target,'resolved':str(q)})
P=Path('/tmp/zfc-intake194/extracted/K217_Exposed_Marker')
for name in ('k217.native.tm','k217.tm','canonicalization.json'):
 assert (C/name).read_bytes()==(P/'machine'/name).read_bytes()
assert (C/'comparison.json').read_bytes()==Path('/tmp/zfc-intake194-opening-comparison/review.json').read_bytes()
actual=H/'data/intake194-fresh/actual.json';assert actual.read_bytes()==Path('/tmp/zfc-intake194/fresh1/actual.json').read_bytes()
read_actual=H/'data/intake194-fresh/review/actual-review.json';assert read_actual.read_bytes()==(O/'actual-review.json').read_bytes()
res={'status':'EXPOSED_MARKER_PUBLICATION_PROSE_REVIEW_PASS','findings':[],'reviewer':'review_upstream_reflection','documents':[d(p)for p in notes],'local_links_checked':len(links),'links':links,'evidence':[d(actual),d(read_actual),d(C/'comparison.json'),d(O/'review.json')],'reviewer_source':d(Path(__file__)),'scope':['Full three maintained notes read against independent ordinary manuscript/code review and own saved-three-leaf semantic audit','Native new-to-primary three-state permutation,all434 rows and both dense conventions correctly attributed to Opening comparison','Exact source/candidate025 identity entails no stacking or new physical saving','Main ordinary Source149/152 calibration separate from fixed13 appendix and three new finite checks','Fixed-core count211 versus203 and as-delivered missing complete AX/compiler/binary scope are accurate; new scratch compiler is a separate prospective follow-up','Divergence clarification correct: closed/halt-free does not imply normal termination','No new full runtime/startup/kernel or<=216 claim','Published tables/maps/actual receipt exact bytes; all direct local Markdown links resolve'],'limitations':'No independent re-audit of all57 placement members or inherited runtime proofs; placement/recovery claims remain root-owned. No delivered execution.'}
(O/'publication-review.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({'review':d(O/'publication-review.json'),'links':len(links)}))
