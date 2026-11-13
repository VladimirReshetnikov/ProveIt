#!/usr/bin/env python3
"""Review pinned AQ17 policy, adapted paired tools and detached toy controls."""
import ast,copy,hashlib,json,re,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[3];BASE=ROOT/'Computability/DiophantineConsistency';RESEARCH=BASE/'research'
TASK=RESEARCH/'ipra-standard-aq17';HIST=TASK/'historical';REFERENCE=RESEARCH/'ipra-standard-current14';TRIAL=BASE/'reviews/ipra-aq17-guarded-author'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
prior=BASE/'reviews/ipra-aq17-guarded-author-independent-audit'
parent_manifest=Path('/tmp/ipra-aq29-fresh-source-closure-v2/manifest.json')
tracked=[Path(__file__),TASK/'paired_plan.py',TASK/'author-additions.json',HIST/'task-policy.json',HIST/'REAL-RUN.md',HIST/'provisional-plan.json',
         TRIAL/'state.json',TRIAL/'terminal-observation.json',prior/'receipt.json',prior/'terminal-observation.json',
         RESEARCH/'aq17-witness-transport/author-additions.json',REFERENCE/'paired_plan.py',parent_manifest]
tracked += sorted((TRIAL/'logs').glob('*.log'))
tracked += [HIST/n for n in ('prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py','run_controls.py','test_prepare.py','test_real_extension.py','test_full_chain.py','test_history.py','test_freeze.py')]
tracked += [REFERENCE/'historical'/n for n in ('prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py')]
tracked += [RESEARCH/'fresh-project-closure'/n for n in ('rebuild.py','compare.py','run_pair.py')]
snapshot={str(p.resolve()):H(p) for p in tracked}
policy=J(HIST/'task-policy.json');manifest=J(TASK/'author-additions.json');source_manifest=RESEARCH/'aq17-witness-transport/author-additions.json';state=J(TRIAL/'state.json')
assert H(HIST/'task-policy.json')=='516dff5fdda1544558cb2d3b77987165854cbe53390c7b31f3f221aeae1f75ba'
assert H(TASK/'author-additions.json')==H(source_manifest)=='96cd989a4abaf88c0c181e14a72946b3af1b58f4efc485a63ff1687c56918378'
assert H(TRIAL/'state.json')=='0ac4cf0425d3a405fdd6bdf5450d6a7602fb8a15479f26547ec68f739c09b3f7'
assert J(TRIAL/'terminal-observation.json')['observed_exit_code']==0
assert J(prior/'receipt.json')['status']=='PASS_INDEPENDENT_AQ17_AUTHOR_ARTIFACT_AUDIT'
assert J(prior/'terminal-observation.json')['observed_exit_code']==0
assert J(prior/'receipt.json')['trial_state_sha256']==H(TRIAL/'state.json')
order=manifest['order'];assert len(order)==len(set(order))==44
expected={n:manifest['axiom_reports'].get(n,[]) for n in order}
assert sum(map(len,expected.values()))==109 and sum(bool(x) for x in expected.values())==34
assert policy['addition_order']==order==[r['module'] for r in state['rows']]
assert policy['sources']==manifest['sources'] and policy['expected_axiom_by_module']==expected
assert policy['target']==order[-1]=='DiophantineConsistency.IPRAStandardAQ17'
assert policy['expected_axiom_names']==expected[order[-1]]==[
 'DiophantineConsistency.IPRAStandardAQ17.literal_equivalence',
 'DiophantineConsistency.IPRAStandardAQ17.selected_foundation_consistency',
 'DiophantineConsistency.IPRAStandardAQ17.literal_iff_translated_consistency']
pattern=re.compile(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",re.M)
logs=[]
for i,row in enumerate(state['rows']):
    path=TRIAL/'logs'/(f'{i:03d}-'+row['module'].replace('.','_')+'.log');logs.append(path)
    text=path.read_text();parsed=pattern.findall(text)
    assert row['exit']==0 and H(path)==row['log_sha256'] and row['source_sha256']==policy['sources'][row['module']]['sha256']
    assert [name for name,_ in parsed]==expected[row['module']] and [list(x) for x in parsed]==row['axiom_reports']
    assert all({v.strip() for v in ax.split(',') if v.strip()}<={'propext','Classical.choice','Quot.sound'} for _,ax in parsed)
# Freeze the exact adapted executable bytes to the reviewed current14 code.
for reference in [REFERENCE/'paired_plan.py']+[REFERENCE/'historical'/n for n in ('prepare.py','freeze.py','rebuild.py','compare.py','run_pair.py')]:
    repo_path=str(reference.relative_to(ROOT))
    pinned=subprocess.run(['git','show','0315f0f3ec:'+repo_path],cwd=ROOT,check=True,capture_output=True).stdout
    assert pinned==reference.read_bytes(),repo_path
files=['rebuild.py','compare.py','run_pair.py']
for name in files:assert (HIST/name).read_bytes()==(REFERENCE/'historical'/name).read_bytes(),name
oldhash='aed46974c461c626aa93781e5e927fb1b63b93d92c51202343ea0e2e3ef08413';newhash='516dff5fdda1544558cb2d3b77987165854cbe53390c7b31f3f221aeae1f75ba'
def adapt(s):return s.replace('ipra-standard-current14','ipra-standard-aq17').replace(oldhash,newhash).replace('current14','aq17')
for old,new in [(REFERENCE/'paired_plan.py',TASK/'paired_plan.py'),(REFERENCE/'historical/prepare.py',HIST/'prepare.py')]:
    assert adapt(old.read_text())==new.read_text(),new
ref=(REFERENCE/'historical/freeze.py').read_text();expected_old=[
 'DiophantineConsistency.IPRAStandardTheory.leibniz','DiophantineConsistency.IPRAStandardTheory.provable_iff',
 'DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_consistency','DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_translated_consistency']
assert all(repr(n) in ref for n in expected_old)
x=adapt(ref);a=x.index('EXPECTED=(');b=x.index('\nH=prepare.digest',a)
x=x[:a]+'EXPECTED=(\n'+''.join('    '+repr(n)+',\n' for n in policy['expected_axiom_names'])+')'+x[b:]
assert x==(HIST/'freeze.py').read_text()
# Independently compare normalized provisional graph to the whole parent:
plan=J(HIST/'provisional-plan.json');parent=J(parent_manifest)
assert H(parent_manifest)=='63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48'
assert plan['parent_manifest_sha256']==H(parent_manifest)
assert plan['status']=='PROVISIONAL_MANIFEST_PLAN' and plan['basis']=='historical' and plan['additional_project_modules']==order
assert len(plan['parent_source_modules_used'])==1209 and set(parent['order'])-set(plan['parent_source_modules_used'])=={'DiophantineConsistency.IPRAAQ29NativeChecks'}
assert plan['parent_source_drift'] is None and len(parent['order'])==1210
# Independent simple adversarial policy coverage checks.
def verify(p):
    if p['addition_order']!=order or set(p['sources'])!=set(order) or p['expected_axiom_by_module']!=expected or p['expected_axiom_names']!=expected[order[-1]]:raise ValueError('policy mismatch')
for kind in ('missing_module','missing_report','silent_module_report','wrong_order'):
    bad=copy.deepcopy(policy)
    if kind=='missing_module':bad['addition_order'].pop(0)
    if kind=='missing_report':bad['expected_axiom_by_module'][order[-1]].pop()
    if kind=='silent_module_report':
        silent=next(n for n in order if not expected[n]);bad['expected_axiom_by_module'][silent]=['forged']
    if kind=='wrong_order':bad['addition_order'][0],bad['addition_order'][1]=bad['addition_order'][1],bad['addition_order'][0]
    try:verify(bad)
    except ValueError:pass
    else:raise AssertionError(('policy mutation accepted',kind))
# Parse runbook without executing any commands or opening the real pair.
book=(HIST/'REAL-RUN.md').read_text();blocks=re.findall(r'```bash\n(.*?)\n```',book,re.S);assert len(blocks)==1
shell=subprocess.run(['bash','-n'],input=blocks[0],capture_output=True,text=True);assert shell.returncode==0,shell.stderr
embedded=re.findall(r"<<'([^']+)'\n(.*?)\n\1",blocks[0],re.S)
assert len(embedded)==5
for _,code in embedded:ast.parse(code)
assert "'--expected-axiom-reports','3'" in book and 'MATCHED_SELECTIVE_PASS 44 affected modules' in book
assert 'observed_exit_code' in book and "p['workspace_head_before']!=p['workspace_head_after']" in book
# Run a detached complete control suite. The only parent tools copied here are
# fixture inputs; neither live parent nor real extension path is modified.
with tempfile.TemporaryDirectory(prefix='aq17-paired-independent-') as td:
    r=Path(td)/'Computability/DiophantineConsistency/research';target=r/'ipra-standard-aq17';target.mkdir(parents=True)
    shutil.copy2(TASK/'paired_plan.py',target/'paired_plan.py');shutil.copy2(TASK/'author-additions.json',target/'author-additions.json')
    dest=target/'historical';dest.mkdir()
    names=['task-policy.json']+[p.name for p in HIST.glob('*.py')]
    for name in names:shutil.copy2(HIST/name,dest/name)
    parenttools=r/'fresh-project-closure';parenttools.mkdir()
    for name in ('rebuild.py','compare.py','run_pair.py'):shutil.copy2(RESEARCH/'fresh-project-closure'/name,parenttools/name)
    inputs=[(TASK/'paired_plan.py',target/'paired_plan.py'),(TASK/'author-additions.json',target/'author-additions.json')]
    inputs.extend((HIST/name,dest/name) for name in names)
    inputs.extend((RESEARCH/'fresh-project-closure'/name,parenttools/name) for name in ('rebuild.py','compare.py','run_pair.py'))
    for original,copied in inputs:assert H(original)==H(copied)
    q=subprocess.run([sys.executable,str(dest/'run_controls.py')],capture_output=True,text=True,timeout=300)
    assert q.returncode==0,(q.stdout,q.stderr)
    detached=J(dest/'control-receipt.json');assert detached['status']=='PASS_HISTORICAL_TOY_CONTROLS' and len(detached['controls'])==10
    assert all(row['exit_code']==0 for row in detached['controls'][:5]) and all(row['exit_code']!=0 for row in detached['controls'][5:])
    for original,copied in inputs:assert H(original)==H(copied)
    control={'exit_code':q.returncode,'stdout':q.stdout,'stderr':q.stderr,'receipt_sha256':H(dest/'control-receipt.json'),'controls':detached['controls']}
assert {str(p.resolve()):H(p) for p in tracked}==snapshot
result={'status':'PASS_INDEPENDENT_AQ17_WORKFLOW_REVIEW','inputs_sha256':snapshot,'modules':44,'reports':109,'silent_modules':10,
 'parent_total_rows':1210,'manifest_only_dependencies':1209,'policy_mutations':4,'detached_controls':control,
 'scope':'Static historical policy and synthetic workflow controls, not a real AQ17 pair, Lean replay, PDF semantics, or transitive/dynamic provenance authentication.'}
out=HERE/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out))
