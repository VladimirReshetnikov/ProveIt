from pathlib import Path
import hashlib,json,difflib
O=Path(__file__).resolve().parent
P=Path('/tmp/zfc-intake194/extracted/K217_Exposed_Marker')
A=Path('/tmp/zfc-intake194/fresh1')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def d(p):return {'path':str(p),'sha256':sha(p)}
def j(p):return json.loads(p.read_text())
r=j(A/'actual.json');assert r['status']=='THREE_SELECTED_LEAVES_AND_EXPECTED_GATES_PASS'
assert [x['name']for x in r['jobs']]==['construct','four-cases','fixed-core']
files=[A/'actual.json',A/'run.py',A/'history/manifest-loop-omitted.diff',A/'history/verify_fixed_core.original.py']
for x in r['jobs']:
 assert x['code']==0 and x['timeout'] is False and x['cap_seconds']==60 and 0<x['seconds']<60
 script=Path(x['argv'][2]);assert sha(script)==x['script_sha256']
 stdout=A/'logs'/(x['name']+'.stdout');stderr=A/'logs'/(x['name']+'.stderr')
 assert stdout.stat().st_size>0 and stderr.read_bytes()==b''
 files += [script,stdout,stderr]
original=(P/'appendix/fixed_core/verify_fixed_core.py').read_text()
assert (A/'history/verify_fixed_core.original.py').read_text()==original
omit="manifest=json.loads((P/'provenance.json').read_text())\nfor r in manifest['files']:\n    assert sha((P/r['artifact']).read_bytes())==r['sha256'],('input identity',r['artifact'])\n"
assert original.count(omit)==1
adapted=original.replace(omit,'# Intake adapter: the delivery provenance-manifest loop is not executed.\n')
assert (A/'packet/appendix/fixed_core/verify_fixed_core.py').read_text()==adapted
expected_diff=''.join(difflib.unified_diff(original.splitlines(True),adapted.splitlines(True),fromfile='verify_fixed_core.original.py',tofile='verify_fixed_core.py'))
assert (A/'history/manifest-loop-omitted.diff').read_text()==expected_diff
for f in ('construct217.py','check_fold217_four_cases.py'):
 assert (P/'code'/f).read_bytes()==(A/'packet/code'/f).read_bytes()
for f in ('baseline218.native.tm','baseline_sites218.json'):
 assert (P/'machine'/f).read_bytes()==(A/'packet/machine'/f).read_bytes();files +=[P/'machine'/f]
for f in ('baseline_dominated203.json','macros.json','fixed13_direct211.json','fixed01_direct210.json','fixed01_reassociated210.json'):
 p=P/'appendix/fixed_core/source'/f;assert p.read_bytes()==(A/'packet/appendix/fixed_core/source'/f).read_bytes();files +=[p]
for f in ('k217.native.tm','k217.tm','sites217.json','prefold218.native.tm'):
 p=A/'outputs/rebuilt'/f;assert p.read_bytes()==(P/'machine'/f).read_bytes();files +=[p]
c=j(A/'outputs/rebuilt/reconstruction.json');f=j(A/'outputs/four-cases.json');k=j(A/'outputs/fixed-core.json')
assert c['working_states']==217 and c['transition_rows']==434 and c['changed_source_addresses']==94
assert c['source_metrics']==dict(dag_nodes=203,leaf_occurrences=4751,maximum_depth=45,maximum_zero_run=6)
assert f['old_working_states']==218 and f['new_working_states']==217 and f['unchanged_mapped_rows']==432
assert [(x['old_state'],x['marker'],x['scanned_bit'],x['new_duration'],x['endpoint_state'],x['endpoint_head'])for x in f['cases']]==[(69,1,0,3,105,1),(69,1,1,1,31,1),(400,0,0,3,104,1),(400,0,1,1,31,1)]
def table(p):
 out={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,di,z=l.split();out[int(q),int(b)]=(int(w),1 if di=='R'else -1,int(z))
 return out
T=table(P/'machine/k217.native.tm')
for case in f['cases']:
 initial={-1:case['marker'],0:case['scanned_bit']};t=initial.copy();q,h=69,0
 for s in case['trace']:
  assert s['state']==q and s['head']==h and s['read']==t[h]
  action=(s['write'],s['move'],s['next']);assert action==T[q,t[h]]
  t[h]=action[0];h+=action[1];q=action[2]
 assert t==initial and (q,h)==(case['endpoint_state'],case['endpoint_head'])
assert f['negative_control']=={'status':'REJECTED','reason':'Unaccounted nonlocal mutation: (0, 0)'}
assert k==j(P/'appendix/fixed_core/source_receipt.json') and k['source_only'] is True
assert [[x['metrics'][z]for z in ('dag_nodes','leaf_occurrences','maximum_depth','maximum_zero_run')]for x in k['reports']]==[[211,4718,46,9],[210,4673,46,9],[210,4673,47,6]]
assert k['reports'][0]['emitted_formulas']==['N(nks(1,3,c+4))','gated V(a,b,c)']
assert k['reports'][1]['emitted_formulas']==['N(nks(0,1,c+2))','gated V(a,b,c)']
assert all(x['outside_AX_primitives_preserved']==186 for x in k['reports'][:2])
for x in ('outputs/rebuilt/reconstruction.json','outputs/four-cases.json','outputs/fixed-core.json'):files +=[A/x]
res={'status':'EXISTING_THREE_SELECTED_LEAVES_SEMANTIC_REVIEW_PASS','findings':[],'reviewer_role':'Independent prior manuscript/code reviewer; not executor of the three delivered leaves','actual':d(A/'actual.json'),'source_review':d(O/'review.json'),'reviewer_source':d(Path(__file__)),'checks':['Three ordered successful processes,60-second caps,empty stderr and nonempty stdout','Exact original two scripts and sole fixed-core provenance-loop omission; unchanged mathematical/data assertions','Selected original/copy data identities and four reconstructed exact artifacts','203/4751 source census and94 changed addresses','All four recorded local traces independently matched to literal rows,exact two-cell tape and endpoint','Explicit initial-halt negative control rejected','Entire fixed-core receipt equals delivered,all three metrics and two exact symbolic formula stacks bound'],'child_seconds':sum(x['seconds']for x in r['jobs']),'files':[d(p)for p in files],'precision_addendum':'The delivered calibration_review phrase composition of normally returning programs must not be read as a termination theorem. Closed/halt-free factors may diverge. The closed-boundary reassociation proof and exact guarded CFG equality preserve both normal results and divergence. Root identified this wording point; original source-only review remains unchanged.','scope':'Saved-record/raw-log/source-adapter/input-output binding plus independent four tiny local traces; no delivered script, startup or full symbolic runtime rerun, no manifest suite, no proof assistant.'}
(O/'actual-review.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({'review':d(O/'actual-review.json'),'actual':d(A/'actual.json'),'seconds':res['child_seconds']},indent=2))
