from pathlib import Path
import hashlib,json,re
R=Path('/home/codex/.codex/worktrees/ec20/Proofs');O=Path(__file__).resolve().parent
H=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'
C=R/'Computability/BusyBeaver/Research/ZFC/candidate-k217/research/cache-return'
def d(p):return {'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
def j(p):return json.loads(p.read_text())
notes=[H/'intake-193.md',H/'intake-193-reproduction.md',H/'intake193-source154-fresh-reproduction.md',C/'README.md']
links=[]
for p in notes:
 for target in re.findall(r'\]\(([^)\s]+)\)',p.read_text()):
  if '://'in target or target.startswith('#'):continue
  q=(p.parent/target.split('#')[0]).resolve();assert q.exists(),(str(p),target)
  links.append({'from':str(p),'target':target,'resolved':str(q)})
a154=j(H/'data/intake193-source154-fresh/actual-review.json')
assert a154['status']=='SAVED_FIVE_THEORY_LEAVES_REVIEW_PASS'
assert a154['semantic_counts']=={'symbolic_block_regressions':1755,'inverse_decoder_fields':49923,'inverse_arithmetic_inputs':100001,'two_element_semantic_checks':40004,'shifted_fields':33282,'shifted_inputs':100001,'distribution_value_pair_sets':65535,'rho6_value_sets':15,'template_BDD_equalities':656,'dual_B_BDD_equalities':8}
x=j(C/'run2/composition.json');assert x['metrics']=={'dag_nodes':203,'leaf_occurrences':4728,'maximum_depth':45,'maximum_zero_run':6}
assert x['guards']==6146 and x['all_retained_CFG_edges']==6141 and x['startup_steps']==312617
assert x['expected_decoder_bindings']==4727 and x['complete_leaf_action_bindings']==4728
assert x['source_replacement']['old_leaves']==26 and x['source_replacement']['new_leaves']==3
f=j(C/'folds/metadata-audit.json');assert f['status']=='PASS' and f['runs'][0]['ordered_pairs']==46872 and f['runs'][0]['candidate_specs']==645408
s153=j(H/'data/intake193-source153/actual-review.json')
refs=[H/'data/intake193-source154-fresh/actual.json',H/'data/intake193-source154-fresh/actual-review.json',H/'data/intake193-source154-fresh/review/review.json',H/'data/intake193-source154-fresh/review/cache-return-transfer.md',H/'data/intake193-source153/actual-review.json',H/'data/intake193-source153/review/review.json',C/'run2/composition.json',C/'peer/review.json',C/'folds/metadata-audit.json']
out={'status':'SCOPED_WRITTEN_INTAKE_AND_CACHE_PROSE_REVIEW_PASS','findings':[],'reviewer_role':'Full Source154 manuscript/selected-code reviewer and five-leaf executor; independent reader of root193 intake/cache prose. Source153 detailed mathematics relies on its separate author/peer lane; not a second full Source153 manuscript review.','documents':[d(p)for p in notes],'evidence':[d(p)for p in refs],'local_links_checked':len(links),'links':links,'scope':['Complete current intake/reproduction/cache README prose read','Source154 positive/negative theorem distinctions checked against prior full review; ordinary proofs versus five finite leaves kept separate','Six Source153 jobs and detailed claims remain attributed to its separate review/evidence','6,146 total guards and6,141 retained CFG edges correctly distinguished','Exact cache interface,common-input AX/compiler/cofinal premise,26→3 replacement and no fresh modified runtime claim','645,408 finite search negatives are not lower bounds or semantic counterexamples','Source155 separately identified; no promotion or<=216 claim','No supplied invocation, new search, runtime or proof-assistant execution'], 'reviewer_source':d(Path(__file__))}
(O/'review.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'review':d(O/'review.json'),'local_links':len(links),'source153_saved_review_status':s153.get('status')},indent=2))
