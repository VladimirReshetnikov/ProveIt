#!/usr/bin/env python3
"""Independent, read-only terminal phase17 evidence readback. No imported helpers."""
from pathlib import Path
from collections import Counter
import copy, hashlib, json, re
C=Path('/tmp/k215-phase17-check');B=C/'build-run1';T=Path('/tmp/k215-phase17-profile-migration');O=Path(__file__).resolve().parent
OLD='7b947b62acf1b5e6ecaef1a7036e998a4ce7e3bd0d0e8a38b0dd73af0225ebb5';NEW='592bb22d65b39f1abe6b59612869c9a632d5c86f36245e22f24c9abf5db061d8';RUNNER='322d0a8869f65258722c388b918210f48d98829c7648eef52105f886387282e6'
M='BusyBeaver.ZFC.DecoderSourceBinding';STD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def profiles(s):return [[n,sorted({a.strip()for a in ax.split(',')if a.strip()})]for n,ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",s)]
def policy(row,rec):
    assert rec['status']=='PASS'and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
    assert sha(rec['log'])==rec['log_sha256'];text=Path(rec['log']).read_text();rs=profiles(text)
    assert 'error:'not in text and 'sorryAx'not in text and all(set(ax)<=STD for _,ax in rs)
    if 'expected_reports'in row:assert rs==row['expected_reports']
    else:assert [n for n,_ in rs]==row['expected_report_names']and row['allowed_report_axioms']==sorted(STD)
    if row.get('warnings_forbidden'):assert 'warning:'not in text
    return rs
assert sha(C/'build.py')==RUNNER and sha(C/'plan-reviewed.json')==NEW and sha(C/'plan.json')==OLD
plan=read(C/'plan-reviewed.json');original=read(C/'plan.json');expected=copy.deepcopy(original)
next(r for r in expected['modules']if r['module']==M)['expected_reports'][0][1]=['propext'];assert plan==expected
outer=read(C/'resume-outer.json');assert outer['status']=='PASS_EXIT_ZERO'and outer['exit_code']==0
assert outer['argv']==['python3','-B',str(C/'build.py'),'--map',str(C/'plan-reviewed.json'),'--out',str(B)]
assert outer['stdout_sha256']==sha(C/'resume.stdout')and outer['stderr_sha256']==sha(C/'resume.stderr')and(C/'resume.stderr').read_bytes()==b''
assert outer['freeze_sha256']==sha(C/'resume-freeze.json');freeze=read(C/'resume-freeze.json')
transition=read(T/'transition.json');exception=read(T/'exception.json')
assert freeze['transition_sha256']==sha(T/'transition.json')and freeze['exception_sha256']==sha(T/'exception.json')
assert transition['status']=='APPLIED_GUARDED_METADATA_PROFILE_TRANSITION'and not transition['attempt137_promoted']
assert exception['module']==M and exception['before_axioms']==[]and exception['after_axioms']==['propext']
assert exception['original_outer_status']=='FAIL'and exception['original_compiler_status']=='PASS'and exception['original_compiler_exit_code']==0
for path,h in transition['original_files'].items():assert sha(T/'original'/Path(path).name)==h
for p in ['plan.json','freeze.json','build-outer.json','build.stdout','build.stderr','build.py']:assert sha(C/p)==sha(T/'original'/p)
assert read(C/'build-outer.json')['status']=='FAIL'
old_before=read(T/'original/before.json');before=read(B/'before.json');old_inventory=read(T/'original/inventory.json');inventory=read(B/'inventory.json');done=read(B/'completed.json');old_done=read(T/'original/completed.json');result=read(B/'result.json')
new_before=copy.deepcopy(old_before);new_before['plan_sha256']=NEW;del new_before['inputs'][str(C/'plan.json')];new_before['inputs'][str(C/'plan-reviewed.json')]=NEW
assert before==new_before and inventory=={**old_inventory,'modules':plan['modules']}
assert len(old_done)==177 and all(done[m]==rec for m,rec in old_done.items())
assert sum(r['origin']=='candidate_fresh'for r in old_done.values())==136
assert result['status']=='PASS'and result['provider_count']==len(done)==len(plan['modules'])==213
assert result['map_sha256']==NEW and result['runner_sha256']==RUNNER
assert result['inventory_sha256']==sha(B/'inventory.json')and result['completed_sha256']==sha(B/'completed.json')
assert inventory['modules']==plan['modules']and inventory['targets']==result['targets']==plan['targets']
selected={r['module']:r for r in plan['modules']};assert set(selected)==set(done)
old={};oldrows={};oldorigin={}
for directory,origin in [(Path('/tmp/k215-phase16-check/primary-run1'),'phase16_primary'),(Path('/tmp/k215-phase16-check/compatibility-run1'),'phase16_compatibility')]:
    prior=read(directory/'result.json');assert prior['status']=='PASS'and prior['completed_sha256']==sha(directory/'completed.json')and prior['inventory_sha256']==sha(directory/'inventory.json')
    for row in read(directory/'inventory.json')['modules']:
        m=row['module'];old[m]=read(directory/'completed.json')[m];oldrows[m]=row;oldorigin[m]=origin
assert len(old)==212
changed={m for m,r in selected.items()if m not in old or(r['source_sha256'],r['imports'])!=(oldrows[m]['source_sha256'],oldrows[m]['imports'])};forced=set(changed)
while True:
    more=forced|{m for m,r in selected.items()if set(r['imports'])&forced}
    if more==forced:break
    forced=more
assert len(changed)==80 and len(forced)==171 and sorted(changed)==result['changed_sources']and sorted(forced)==result['force_basis_rebuild']
reports={};fresh=[];reuse=[];warnings=[];clients=[];fresh_raw=set()
for row in plan['modules']:
    m=row['module'];rec=done[m];workspace=B/'workspace'/(m.replace('.','/')+'.lean');obj=B/'objects'/(m.replace('.','/')+'.olean')
    assert sha(row['source'])==sha(workspace)==row['source_sha256']==rec['source_sha256']and sha(obj)==rec['object_sha256']
    assert rec['dependencies']=={d:done[d]['object_sha256']for d in row['imports']if d!='Init'};reports[m]=policy(row,rec)
    if m in old and m!=M:assert row['expected_reports']==profiles(Path(old[m]['log']).read_text())
    if not m.startswith(('BusyBeaver.','FirstOrder.','ZF.','BoundedZFCConsistency.')):
        clients.append(m);assert row['warnings_forbidden']and'warning:'not in Path(rec['log']).read_text()
        if m in old:assert row['source_sha256']==oldrows[m]['source_sha256']
    if rec['origin']=='candidate_fresh':
        fresh.append(m);assert m in forced and not obj.is_symlink();raw=Path(rec['log']).with_name('record.json');assert read(raw)==rec;fresh_raw.add(raw)
        assert rec['command']==['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-j1','-M12288','--root='+str(B/'workspace'),'-o',str(obj),str(workspace)]
        assert rec['timeout_seconds']==(900 if'KSites215Batch'in m else 120)and rec['memory_mebibytes']==12288
        assert sha(raw.parent/workspace.name)==row['source_sha256']and rec['reports']==reports[m]
    else:
        reuse.append(m);assert m not in forced and rec=={**old[m],'origin':oldorigin[m]}and obj.is_symlink()
    messages=[line.split('warning:',1)[1].strip()for line in Path(rec['log']).read_text().splitlines()if'warning:'in line]
    if messages:warnings.append({'module':m,'origin':rec['origin'],'messages':messages,'preexisting':[message in Path(old[m]['log']).read_text()if m in old else False for message in messages]})
assert len(fresh)==171 and len(reuse)==42 and result['fresh_modules']==fresh and result['reused_modules']==reuse and len(clients)==14
assert sum(len(reports[m])for m in read('/tmp/k215-phase16-check/primary-run1/inventory.json')['targets']if m not in['BusyBeaver.ZFC.KEndpoint215','BusyBeaver.ZFC.KDecoderPrefix215','BusyBeaver.ZFC.PSCCalibration'])==70
assert sum(len(reports[m])for m in['WFModelCompat12','ZFNativeCompat12'])==10 and len(reports['BusyBeaver.ZFC.WFTheory'])==5
assert reports[M][0][1]==['propext']and result['new_module_actual_profiles']=={m:reports[m]for m in selected if m not in old}
audit_reports=[]
for row,rec in zip(plan['audits'],result['audits']):
    d=B/('audit-'+row['module']);assert rec==read(d/'record.json')and rec['warnings']==0 and rec['source_sha256']==row['source_sha256']==sha(row['source'])==sha(rec['source'])
    assert sha(d/(row['module']+'.olean'))==rec['object_sha256']and rec['dependencies']=={m:r['object_sha256']for m,r in done.items()}
    audit_reports.extend(policy(row,rec))
assert len(plan['audits'])==len(result['audits'])==2 and len(audit_reports)==10
all_attempts=list((B/'attempts').glob('*/record.json'));failedraw=B/'attempts/137-BusyBeaver.ZFC.DecoderSourceBinding/record.json';assert len(all_attempts)==172 and set(all_attempts)-fresh_raw=={failedraw}
for raw in all_attempts:
    rec=read(raw);assert rec['status']=='PASS'and rec['exit_code']==0 and not rec['timed_out']and sha(rec['log'])==rec['log_sha256']
for name in['record.json','compiler.log','assumption-profile-discrepancy.json','DecoderSourceBinding.lean']:assert sha(failedraw.parent/name)==sha(T/'original/attempt137'/name)
assert done[M]['log']!=str(failedraw.parent/'compiler.log')
sites=['BusyBeaver.ZFC.KSites215Batch'+str(i).zfill(3)for i in range(9)];assert all(m in fresh and m in old_done and done[m]==old_done[m]for m in sites)
site_json=next(p for p in plan['present_inputs']if p.endswith('/candidate-k215/sites215.json'));leaves=read(site_json);assert len(leaves)==4751
counts=Counter(row[1]for row in leaves);assert dict(counts)=={'CD':1425,'CB':98,'CI':1900,'CC':1327,'CH':1}and sum(2 if row[1]=='CD'else 1 for row in leaves)==6176
blocks={}
for m in sites:
    text=Path(selected[m]['source']).read_text();assert selected[m]['source_sha256']==oldrows[m]['source_sha256']
    for num,rev,fwd in re.findall(r'theorem block_(\d+)\s*:\s*allSites \(KSim.checkEdge tm215\) \[([^]]*)\]\s*\(descend KSource215.t215 \[([^]]*)\]\) = true := by\s*exact KFastSites215.allSites_of_fast \(by decide \+kernel\)',text):
        bits=lambda s:[x.strip()for x in s.split(',')if x.strip()];assert bits(rev)==list(reversed(bits(fwd)))and int(num)not in blocks;blocks[int(num)]=''.join('1'if x=='true'else'0'for x in bits(fwd))
assert set(blocks)==set(range(105))and all(sum(path.startswith(prefix)for prefix in blocks.values())==1 for path,_,_ in leaves)
root=Path(selected['BusyBeaver.ZFC.KSites215']['source']).read_text();assert sorted(map(int,re.findall(r'\bblock_(\d+)\b',root)))==list(range(105))and'KSource215.t215_eq all_sites'in root
closure=set()
def visit(m):
    if m=='Init'or m in closure:return
    closure.add(m)
    for d in selected[m]['imports']:visit(d)
visit('BusyBeaver.ZFC.KEndpoint215');assert len(closure)==174 and sum(Path(selected[m]['source']).stat().st_size for m in closure)==1749188
for path,h in before['inputs'].items():assert sha(path)==h
assert len(plan['present_inputs'])==54 and len(plan['absent_inputs'])==7
for path in plan['absent_inputs']:assert not Path(path).exists()and not Path(path).is_symlink()
assert result['historical_raw_coverage']==before['historical_raw_coverage'];coverage=result['historical_raw_coverage'];assert len(coverage)==212 and sum(r['raw_record']is not None for r in coverage.values())==162
for row in coverage.values():assert sha(row['accepted_source'])==oldrows[next(m for m,r in coverage.items()if r is row)]['source_sha256']
receipt={'status':'PASS_INDEPENDENT_RESUMED_ACTUAL_READBACK','helper_sha256':sha(__file__),'runner_sha256':RUNNER,'old_plan_sha256':OLD,'reviewed_plan_sha256':NEW,'result_sha256':sha(B/'result.json'),'resume_outer_sha256':sha(C/'resume-outer.json'),'resume_freeze_sha256':sha(C/'resume-freeze.json'),'transition_sha256':sha(T/'transition.json'),'exception_sha256':sha(T/'exception.json'),'providers':213,'fresh':171,'reused':42,'typed_clients':14,'old_primary_client_reports':70,'old_compatibility_reports':10,'WFTheory_reports':5,'endpoint_reports':audit_reports,'endpoint_modules':174,'endpoint_source_bytes':1749188,'preserved_completed':177,'preserved_fresh':136,'preserved_phase16_reuses':41,'site_batches_fresh_and_preserved':9,'site_blocks':105,'site_leaves':4751,'site_outcomes':6176,'compiler_provider_invocations':172,'extra_original_attempt':'137: compiler PASS exit0, exact-profile gate FAIL; source_tree_eq []→[propext] explicitly reviewed','original_failure_preserved':True,'additional_pins':54,'absences':7,'warning_occurrences':sum(len(r['messages'])for r in warnings),'fresh_warning_occurrences':sum(len(r['messages'])for r in warnings if r['origin']=='candidate_fresh'),'all_fresh_warning_headlines_preexisted':all(all(r['preexisting'])for r in warnings if r['origin']=='candidate_fresh'),'warnings':warnings,'compiler_execution':False,'supplied_code_execution':False,'scope':'Direct readback of all current213source/workspace/object/dependency/log bindings, exact profiles, frozen inputs, retained progress and preserved failure. Finite site-list/partition source census only; no machine execution.'}
(O/'review.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
