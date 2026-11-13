#!/usr/bin/env python3
"""Read-only workflow pin/graph checks and independent toy subprocess controls."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

if not __debug__:
    raise RuntimeError('audit requires Python assertions enabled')

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
TASK=ROOT/'Computability/DiophantineConsistency'
HIST=TASK/'research/ipra-standard-aq22/historical'
PLANNER=HIST.parent/'paired_plan.py'
PACKET=TASK/'reviews/ipra-aq22-guarded-author'
AUTHOR_AUDIT=TASK/'reviews/ipra-aq22-guarded-author-independent-audit/receipt.json'
OLD=Path('/tmp/ipra-aq29-fresh-source-closure-v2')
AUTHOR=Path('/tmp/ipra-aq29-fresh-project-pair/author/state.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert len(sys.argv)==2 and len(sys.argv[1])==40
workflow_commit=sys.argv[1]
files=[PLANNER]+[HIST/n for n in ('task-policy.json','prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py','run_controls.py','test_history.py','test_prepare.py','test_freeze.py','test_real_extension.py','test_full_chain.py')]
before={str(p.relative_to(ROOT)):H(p) for p in files}
for p in files:
    raw=subprocess.check_output(['git','-C',str(ROOT),'show',workflow_commit+':'+str(p.relative_to(ROOT))])
    assert hashlib.sha256(raw).hexdigest()==H(p), ('workflow differs from commit',str(p))
assert H(HIST/'task-policy.json')=='0d80d3899a9b0d2356e16e4c7cc81ec72fe792ea1a1ee2e336f3e92373b4a6b1'
assert H(PACKET/'author-additions.json')=='3c5df040f94803b19ccbed14ec93be2e3de2e16ed9c31efd9bcfb531373200df'
assert H(AUTHOR_AUDIT)=='ae8bf7787034683f1180375891a0ee637d882c7fc0101704278c3161d6dadf16'
policy=json.loads((HIST/'task-policy.json').read_text());author=json.loads((PACKET/'author-additions.json').read_text())
assert author['source_commit']=='bd19027b6835198b97bd58b5d8cb58c1849fcd99'
assert policy['addition_order']==author['order'] and len(author['order'])==37
assert policy['sources']==author['sources']
reports={n:author['axiom_reports'].get(n,[]) for n in author['order']}
assert policy['expected_axiom_by_module']==reports and sum(map(len,reports.values()))==94
assert policy['expected_axiom_names']==reports[policy['target']] and policy['target']==author['order'][-1]
for name in author['order']:
    row=author['sources'][name]
    raw=subprocess.check_output(['git','-C',str(ROOT),'show',author['source_commit']+':'+row['workspace_path']])
    assert hashlib.sha256(raw).hexdigest()==row['sha256']
    assert H(PACKET/'src'/Path(*name.split('.')).with_suffix('.lean'))==row['sha256']
print('PASS: exact source and ordered diagnostic pins',flush=True)
sys.path.insert(0,str(HIST))
import prepare
assert prepare.POLICY_SHA256==H(HIST/'task-policy.json')
assert H(OLD/'manifest.json')=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert H(AUTHOR)=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
old=json.loads((OLD/'manifest.json').read_text()); state=json.loads(AUTHOR.read_text())
assert len(old['order'])==1210 and [r['module'] for r in state['records']]==old['order']
terminal=old['order'][-1]
assert terminal=='DiophantineConsistency.IPRAAQ29NativeChecks'
assert all(terminal not in author['sources'][n]['imports'] for n in author['order'])
new=copy.deepcopy(old);new['order']+=author['order'];new['sources'].update(author['sources']);new['target']=policy['target'];new['project_modules']=len(new['order']);new['parent_source_count']=len(old['order']);new['expected_axiom_names']=policy['expected_axiom_names'];new['expected_axiom_by_module']=reports
new['target_policy_sha256']=H(HIST/'task-policy.json')
prepare.verify_policy(new)
for key in ('source','report','order'):
    bad=copy.deepcopy(new)
    if key=='source':bad['sources'][author['order'][0]]['sha256']='0'*64
    elif key=='report':bad['expected_axiom_by_module'][author['order'][-1]][0]='Wrong.name'
    else:bad['order'][-2],bad['order'][-3]=bad['order'][-3],bad['order'][-2]
    try:prepare.verify_policy(bad)
    except ValueError:pass
    else:raise AssertionError(('failed to reject modified policy input',key))
selected=prepare.select(old,new,state['records'])
assert selected['unaffected']==old['order'] and selected['affected']==author['order']
for label,changed_old,changed_new,records in (
    ('missing terminal record',old,new,state['records'][:-1]),
    ('reordered last records',old,new,state['records'][:-2]+[state['records'][-1],state['records'][-2]]),
):
    try:prepare.select(changed_old,changed_new,records)
    except ValueError:pass
    else:raise AssertionError(('failed to reject',label))
wrong=copy.deepcopy(new);wrong['sources'][terminal]['sha256']='0'*64
try:prepare.select(old,wrong,state['records'])
except ValueError:pass
else:raise AssertionError('failed to reject changed terminal source')
print('PASS: 1210-row structural selection and terminal adversarial controls',flush=True)
rows=[]
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
for name in ('test_history.py','test_prepare.py','test_freeze.py','test_real_extension.py','test_full_chain.py'):
    for opt in (False,True):
        command=[sys.executable]+(['-O'] if opt else [])+[str(HIST/name)]
        q=subprocess.run(command,cwd=HIST,env=env,capture_output=True,text=True,timeout=240)
        if opt:
            assert q.returncode!=0 and 'controls require Python assertions enabled' in q.stderr,(name,q.returncode,q.stderr)
        else: assert q.returncode==0,(name,q.returncode,q.stdout,q.stderr)
        rows.append({'name':name,'optimized':opt,'exit_code':q.returncode,'stdout':q.stdout,'stderr':q.stderr})
    print('PASS: toy control',name,flush=True)
assert {str(p.relative_to(ROOT)):H(p) for p in files}==before
assert H(AUTHOR)=='b9ab036bf00296c9491ef6f06eb44aca805b51ab36f0d48e090d5620a55f6153'
receipt={'status':'PASS_INDEPENDENT_WORKFLOW_TOY_AUDIT','workflow_commit':workflow_commit,'input_hashes':before,
         'author_manifest_sha256':H(PACKET/'author-additions.json'),'author_independent_audit_sha256':H(AUTHOR_AUDIT),
         'historical_parent_manifest_sha256':H(OLD/'manifest.json'),'historical_author_state_sha256':H(AUTHOR),
         'parent_modules_structurally_checked':len(old['order']),'terminal_parent_module':terminal,
         'additions':author['order'],'exact_ordered_diagnostic_occurrences':[x for n in author['order'] for x in reports[n]],
         'test_subprocesses':rows,'scope':'Source policy and structural audit plus synthetic toy controls, not a real parent-pair replay or proof of parent pair completion; real parent provider and peer remain separate evidence.'}
out=HERE/'receipt.json';assert not out.exists();out.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print('PASS_INDEPENDENT_WORKFLOW_TOY_AUDIT',H(out),flush=True)
