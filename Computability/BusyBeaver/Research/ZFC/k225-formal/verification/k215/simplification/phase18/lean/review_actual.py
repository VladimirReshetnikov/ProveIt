#!/usr/bin/env python3
"""Owned read-only phase18 twice-resumed actual-result audit; no compiler/imported helper execution.

Run only after terminal PASS and a saved outer exit-zero record. Reads the frozen
selected scope and preserved actual evidence, then writes its own review/copy map.
"""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, re

R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
C=Path('/tmp/k215-phase18-check');B=C/'build-run1'
RUNNER_SHA='71bd42b1cad2f485581620bb9b8c7d196e30447a101546077767642d065e0c1a'
ORIGINAL_RUNNER_SHA='6d36aefb6bfffe718ae244dd954de5a9c6e9e67d738daff2436eb0a2428f9a19'
T=Path('/tmp/k215-phase18-budget-transition');O=T/'original'
I=Path('/tmp/k215-phase18-session-interruption');IO=I/'original'
PLAN_SHA='df0dbde51be55370f466af3a61f777f81ecda2748b319396a3270f8ff1026977'
SUPERVISOR=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
SUPERVISOR_SHA='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
STD={'propext','Classical.choice','Quot.sound'}
ROOTS=['Computability/BusyBeaver/Lean','Logic/FirstOrder/Lean','SetTheory/ZF/Lean','SetTheory/BoundedConsistency/Lean']
BASIS=[(Path('/tmp/k215-phase17-check/build-run1'),'phase17_checked',213,'0ece73d070ab23aee17cf6067d9b9850bd657f1c63523c0567c1fe4ced66f1ee')]
RAW_SCOPE='Pinned accepted phase17 aggregate, workspace source, object and log; adjacent original raw record additionally checked when present.'

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def profiles(text):return [[n,sorted({a.strip()for a in ax.split(',')if a.strip()})]for n,ax in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",text)]
def strip(text):
    out=[];i=0;depth=0
    while i<len(text):
        if text[i:i+2]=='/-':depth+=1;i+=2
        elif depth and text[i:i+2]=='-/':depth-=1;i+=2
        elif depth:
            if text[i]=='\n':out.append('\n')
            i+=1
        elif text[i:i+2]=='--':
            j=text.find('\n',i);i=len(text)if j<0 else j
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
        else:out.append(text[i]);i+=1
    assert depth==0
    return ''.join(out)
def imports(p):return [m for line in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)',strip(Path(p).read_text()))for m in line.split()]
def policy(row,rec):
    assert rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
    assert sha(rec['log'])==rec['log_sha256'];text=Path(rec['log']).read_text();actual=profiles(text)
    assert 'error:' not in text and 'sorryAx' not in text
    assert all(set(ax)<=STD for _,ax in actual)
    if 'expected_reports'in row:assert actual==row['expected_reports'],(row['module'],'exact profile mismatch')
    else:
        assert [n for n,_ in actual]==row['expected_report_names']
        assert row['allowed_report_axioms']==sorted(STD)
    if row.get('warnings_forbidden'):assert 'warning:' not in text
    return actual

def resume_history():
    # Read original raw statuses and immutable transition snapshots; never promote failure019.
    assert sha(T/'transition.json')=='eeecb22d1b01c2b1ef8ada73ae902fb3ebebc724149d5f4d87521a9428e80ede'
    assert sha(C/'resume-freeze.json')=='c4938972e812d9501eaf947c689eb5f6d333da94533a47a3c1c2888075a04f2d'
    original=(C/'build.py').read_bytes();oldline=b"timeout=900 if 'KSites215Batch' in m else 120"
    newline=b"timeout=900 if 'KSites215Batch' in m or 'KSource215FwdCheck' in m else 120"
    assert original.count(oldline)==1 and (C/'build-forward-budget.py').read_bytes()==original.replace(oldline,newline)
    transition=read(T/'transition.json');rf=read(C/'resume-freeze.json')
    assert transition['status']=='RESOURCE_ONLY_OWNER_MIGRATION' and rf['status']=='FROZEN_RESOURCE_ONLY_RESUME'
    assert transition['original_runner_sha256']==ORIGINAL_RUNNER_SHA and transition['resumed_runner_sha256']==RUNNER_SHA and transition['plan_sha256']==PLAN_SHA
    for p,h in rf['files'].items():assert sha(p)==h,p
    for current,row in transition['snapshots'].items():
        assert sha(row['snapshot'])==row['sha256']
        if current not in [str(B/'before.json'),str(B/'completed.json')]:assert sha(current)==row['sha256']
    old=read(O/'build-run1/before.json');expected={**old,'runner_sha256':RUNNER_SHA,'inputs':dict(old['inputs'])}
    assert expected['inputs'].pop(str(C/'build.py'))==ORIGINAL_RUNNER_SHA
    expected['inputs'][str(C/'build-forward-budget.py')]=RUNNER_SHA
    pref=read(C/'budget-preflight-run1/preflight.json')
    assert expected=={k:pref[k]for k in old}==read(B/'before.json')
    assert sha(O/'build-run1/before.json')==transition['old_before_sha256'] and sha(B/'before.json')==transition['new_before_sha256']
    assert sha(C/'budget-preflight-run1/preflight.json')==transition['preflight_sha256']
    assert sha(B/'inventory.json')==sha(O/'build-run1/inventory.json')==transition['inventory_sha256']
    assert sha(O/'build-run1/completed.json')==transition['completed_sha256']
    assert pref['status']=='PASS_METADATA_PREFLIGHT_NO_COMPILER_EXECUTION'
    po=read(C/'budget-preflight-outer.json')
    assert po['status']=='PASS_EXIT_ZERO' and po['exit_code']==0 and po['stdout_sha256']==sha(C/'budget-preflight.stdout')==sha(C/'budget-preflight-run1/preflight.json')
    assert po['launcher_sha256']==sha('/tmp/k215-phase18-integration/run_budget_once.py') and po['helper_pin_sha256']==sha(C/'budget-helper-pin.json')
    assert transition['migration_helper_sha256']==sha('/tmp/k215-phase18-integration/migrate_budget_owner.py')
    assert po['stderr_sha256']==sha(C/'budget-preflight.stderr') and not(C/'budget-preflight.stderr').read_bytes()
    assert po['argv']==['python3','-B',str(C/'build-forward-budget.py'),'--map',str(C/'plan.json'),'--out',str(C/'budget-preflight-run1'),'--check-plan']
    initial=read(O/'build-run1/completed.json');done=read(B/'completed.json')
    assert len(initial)==23 and Counter(r['origin']for r in initial.values())=={'candidate_fresh':18,'phase17_checked':5}
    assert all(done[m]==r for m,r in initial.items())
    fo=read(O/'build-outer.json');assert fo['status']=='FAIL' and fo['exit_code']==1
    assert fo['stdout_sha256']==sha(O/'build.stdout') and fo['stderr_sha256']==sha(O/'build.stderr')
    assert fo['argv']==['python3','-B',str(C/'build.py'),'--map',str(C/'plan.json'),'--out',str(B)]
    failed=O/'build-run1/attempts/019-BusyBeaver.ZFC.KSource215FwdCheck12';rec=read(failed/'record.json');m=rec['module']
    assert m=='BusyBeaver.ZFC.KSource215FwdCheck12' and m not in initial and rec['status']=='FAIL' and rec['exit_code']==-9 and rec['timed_out']
    assert rec['timeout_seconds']==120 and rec['object_sha256']is None and rec['warnings']==0 and rec['reports']==[]
    assert sha(rec['log'])==rec['log_sha256']==sha(failed/'compiler.log') and not(failed/'compiler.log').read_bytes()
    assert sha(failed/'KSource215FwdCheck12.lean')==rec['source_sha256']==done[m]['source_sha256']
    assert rec['dependencies']==done[m]['dependencies'] and rec['command']==done[m]['command']
    assert Path(done[m]['log']).parent.name=='020-'+m and done[m]['timeout_seconds']==900 and done[m]['status']=='PASS'
    assert re.findall(r'(?m)^FAIL (\S+) ',(O/'build.stdout').read_text())==[m]
    context=[]
    paths=[T/'transition.json',C/'budget-helper-pin.json',C/'budget-preflight-run1/preflight.json',C/'budget-preflight-outer.json',C/'budget-preflight.stdout',C/'budget-preflight.stderr',Path('/tmp/k215-phase18-integration/migrate_budget_owner.py'),Path('/tmp/k215-phase18-integration/run_budget_once.py')]
    paths += [Path(row['snapshot'])for row in transition['snapshots'].values()]
    for p in paths:
        destination='resource/original/'+str(p.relative_to(O))if p.is_relative_to(O)else'resource/'+p.name
        context.append({'source':str(p),'destination':destination,'sha256':sha(p),'bytes':p.stat().st_size})
    assert len({r['destination']for r in context})==len(context)
    return initial,transition,context

def interruption_history():
    # The executor's143 is not a known compiler exit. Never accept partial071's object.
    assert sha(I/'interruption.json')=='85d5000b71ec39a0f07612f695a5a6b55014fd9603df17e336542e3435fe381f'
    assert sha(C/'resume2-freeze.json')=='26f1f1824bb3a53346c90a11608286f2cd0079b9e12fba4cb3976bed5ac816c5'
    history=read(I/'interruption.json');freeze2=read(C/'resume2-freeze.json')
    assert history['status']=='PRESERVED_EXECUTOR_SESSION_INTERRUPTION'
    assert history['observed_exec_session']==7048 and history['observed_executor_exit_code']==143
    assert history['runner_outer_receipt_exists']is False and history['compiler_exit_status_known']is False
    assert not(C/'resume-outer.json').exists() and not(C/'resume-outer.json').is_symlink()
    assert history['owner_unchanged'] and history['proof_sources_profiles_and_plan_unchanged']
    assert history['helper_sha256']==sha('/tmp/k215-phase18-integration/preserve_interruption.py')
    assert freeze2['status']=='FROZEN_DETACHED_RESUME_SAME_OWNER' and freeze2['runner_and_owner_unchanged']
    for p,h in freeze2['files'].items():assert sha(p)==h,p
    for current,row in history['snapshots'].items():
        assert sha(row['snapshot'])==row['sha256']
        if current!=str(B/'completed.json'):assert sha(current)==row['sha256']
    assert sha(B/'before.json')==sha(IO/'build-run1/before.json')==history['before_sha256']
    assert sha(B/'inventory.json')==sha(IO/'build-run1/inventory.json')==history['inventory_sha256']
    assert sha(IO/'build-run1/completed.json')==history['completed_sha256']==freeze2['initial_completed_sha256']
    retained=read(IO/'build-run1/completed.json');done=read(B/'completed.json')
    assert len(retained)==153 and Counter(r['origin']for r in retained.values())=={'candidate_fresh':69,'phase17_checked':84}
    assert all(done[m]==r for m,r in retained.items())
    assert (history['completed_providers'],history['completed_fresh'],history['completed_reuses'])==(153,69,84)
    assert (history['interrupted_stream_checks'],history['interrupted_stream_passes'],history['interrupted_stream_reuses'])==(52,51,79)
    assert (history['next_attempt'],history['remaining_fresh'],history['remaining_reuses'])==(72,38,23)
    partial=IO/'build-run1/attempts/071-BusyBeaver.ZFC.KSites215Batch002';raw=read(partial/'record.json');m=raw['module']
    assert m=='BusyBeaver.ZFC.KSites215Batch002' and m not in retained
    assert history['partial_attempt']=='071-'+m and history['partial_module']==m and history['interrupted_partial_status']=='COMPILING'
    assert raw['status']=='COMPILING' and 'exit_code'not in raw and 'object_sha256'not in raw
    assert not(partial/'compiler.log').read_bytes() and sha(raw['log'])==sha(partial/'compiler.log')
    assert sha(partial/'KSites215Batch002.lean')==raw['source_sha256']==done[m]['source_sha256']
    assert raw['timeout_seconds']==900 and raw['dependencies']==done[m]['dependencies'] and raw['command']==done[m]['command']
    assert Path(done[m]['log']).parent.name=='072-'+m and done[m]['status']=='PASS' and done[m]['timeout_seconds']==900
    assert history['physical_unaccepted_object']=={'present':True,'sha256':'bde2c88e3d361922a1caac548d75b68dfe81e97c4b18d320363460b29ab79ea6','accepted':False}
    # That physical hash is an observation in the pinned preservation receipt, not an accepted proof object.
    launch=read(C/'resume2-launch.json')
    assert launch['status']=='DETACHED_SUPERVISOR_LAUNCHED_NOT_COMPLETED' and launch['start_new_session']is True
    assert launch['pid']==launch['session_id']==4044177
    assert launch['argv']==['python3','-B','/tmp/k215-phase18-integration/run_detached_resume.py']
    assert launch['freeze_sha256']==sha(C/'resume2-freeze.json') and launch['initial_completed_sha256']==history['completed_sha256']
    assert launch['starter_sha256']==sha('/tmp/k215-phase18-integration/start_detached_resume.py')
    assert launch['launcher_sha256']==sha('/tmp/k215-phase18-integration/run_detached_resume.py')
    assert launch['completion_receipt']==str(C/'resume2-outer.json')
    assert read(C/'resume2-launcher.stdout')==read(C/'resume2-outer.json') and not(C/'resume2-launcher.stderr').read_bytes()
    paths=[I/'interruption.json',C/'resume2-launch.json',Path('/tmp/k215-phase18-integration/preserve_interruption.py'),Path('/tmp/k215-phase18-integration/run_detached_resume.py'),Path('/tmp/k215-phase18-integration/start_detached_resume.py'),C/'resume2-launcher.stdout',C/'resume2-launcher.stderr']
    paths += [Path(row['snapshot'])for row in history['snapshots'].values()]
    context=[]
    for p in paths:
        destination='interruption/original/'+str(p.relative_to(IO))if p.is_relative_to(IO)else'interruption/'+p.name
        context.append({'source':str(p),'destination':destination,'sha256':sha(p),'bytes':p.stat().st_size})
    assert len(context)==19 and len({r['destination']for r in context})==19
    return retained,history,context

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--outer',type=Path,required=True);parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parent/'review-resumed-v2.json');args=parser.parse_args()
    assert sha(C/'build-forward-budget.py')==RUNNER_SHA and sha(C/'build.py')==ORIGINAL_RUNNER_SHA and sha(C/'plan.json')==PLAN_SHA
    assert sha(SUPERVISOR)==SUPERVISOR_SHA and sha(LEAN)==LEAN_SHA
    freeze=read(C/'freeze.json');assert freeze['files']['build.py']==ORIGINAL_RUNNER_SHA and freeze['files']['plan.json']==PLAN_SHA
    outer=read(args.outer);assert outer['status']=='PASS_EXIT_ZERO' and outer['exit_code']==0
    assert outer['launcher_sha256']==sha('/tmp/k215-phase18-integration/run_detached_resume.py') and outer['interruption_sha256']==sha(I/'interruption.json')
    assert outer['argv']==['python3','-B',str(C/'build-forward-budget.py'),'--map',str(C/'plan.json'),'--out',str(B)]
    assert outer['stdout_sha256']==sha(C/'resume2.stdout') and outer['stderr_sha256']==sha(C/'resume2.stderr')
    assert outer['freeze_sha256']==sha(C/'resume2-freeze.json') and (C/'resume2.stderr').read_bytes()==b''
    initial,transition,resource_history=resume_history()
    retained,interruption,interruption_context=interruption_history()
    plan=read(C/'plan.json');before=read(B/'before.json');result=read(B/'result.json');inventory=read(B/'inventory.json');done=read(B/'completed.json')
    assert result['status']=='PASS' and result['runner_sha256']==before['runner_sha256']==RUNNER_SHA
    assert result['map_sha256']==before['plan_sha256']==PLAN_SHA
    assert result['inventory_sha256']==sha(B/'inventory.json') and result['completed_sha256']==sha(B/'completed.json')
    assert result['source_transitive_reuse_only'] and result['all_source_object_dependency_log_toolchain_inputs_postchecked']
    rows=plan['modules'];selected={r['module']:r for r in rows};assert len(rows)==len(selected)==len(done)==214
    assert inventory=={'modules':rows,'targets':plan['targets'],'external_imports':['Init']}
    assert result['targets']==before['targets']==plan['targets'] and set(done)==set(selected)
    old={};oldrows={};oldorigin={};coverage={};prior_toolchain=None
    for d,origin,count,pin in BASIS:
        assert sha(d/'result.json')==pin;prior=read(d/'result.json');inv=read(d/'inventory.json');completed=read(d/'completed.json')
        assert prior['status']=='PASS' and len(inv['modules'])==len(completed)==count
        assert prior['inventory_sha256']==sha(d/'inventory.json') and prior['completed_sha256']==sha(d/'completed.json')
        toolchain=read(d/'toolchain.json')
        if prior_toolchain is None:prior_toolchain=toolchain
        else:assert prior_toolchain==toolchain
        for row in inv['modules']:
            m=row['module'];rec=completed[m];source=d/'workspace'/(m.replace('.','/')+'.lean');obj=d/'objects'/(m.replace('.','/')+'.olean')
            assert sha(source)==row['source_sha256']==rec['source_sha256'] and imports(source)==row['imports']
            assert sha(obj)==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256']
            assert rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
            assert rec['dependencies']=={n:completed[n]['object_sha256']for n in row['imports']if n!='Init'}
            rawpath=Path(rec['log']).with_name('record.json');raw=read(rawpath)if rawpath.is_file()else None
            if raw is not None:
                for key in ['module','source_sha256','dependencies','log_sha256','status']:assert raw[key]==rec[key]
                if 'object_sha256'in raw:assert raw['object_sha256']==rec['object_sha256']
                for key in ['command','exit_code','timed_out']:
                    if key in rec:assert raw[key]==rec[key]
                assert raw['exit_code']==0 and not raw['timed_out'] and raw['command'][:3]==[str(LEAN),'-j1','-M12288']
            coverage[m]={'basis':str(d),'accepted_source':str(source),'log':rec['log'],'raw_record':str(rawpath)if raw is not None else None,'raw_has_object_hash':bool(raw is not None and 'object_sha256'in raw),'scope':RAW_SCOPE}
            if m in old:assert oldrows[m]['source_sha256']==row['source_sha256'] and oldrows[m]['imports']==row['imports'] and old[m]['object_sha256']==rec['object_sha256']
            old[m]=rec;oldrows[m]=row;oldorigin[m]=origin
    assert len(old)==213
    assert coverage==before['historical_raw_coverage']==result['historical_raw_coverage']
    assert sum(v['raw_record']is not None for v in coverage.values())==179
    assert sum(v['raw_record']is None for v in coverage.values())==34
    missing_raw_object_hash=sum(v['raw_record']is not None and not v['raw_has_object_hash']for v in coverage.values())
    assert read(B/'toolchain.json')==prior_toolchain
    for key in ['lean','lake','Init.olean','project_toolchain']:
        row=prior_toolchain[key];assert sha(row['path'])==row['sha256']
    changed={m for m,r in selected.items()if m not in old or(r['source_sha256'],r['imports'])!=(oldrows[m]['source_sha256'],oldrows[m]['imports'])}
    forced=set(changed)
    while True:
        more=forced|{m for m,r in selected.items()if set(r['imports'])&forced}
        if more==forced:break
        forced=more
    assert len(changed)==15 and len(forced)==107
    assert sorted(changed)==plan['expected']['changed_sources']==before['changed_sources']==result['changed_sources']
    assert sorted(forced)==plan['expected']['fresh_by_source_transitivity']==before['force_basis_rebuild']==result['force_basis_rebuild']
    visited=set();order=[]
    def visit(m):
        if m=='Init' or m in visited:return
        assert m in selected
        for d in selected[m]['imports']:visit(d)
        visited.add(m);order.append(m)
    for m in plan['targets']:visit(m)
    assert order==[r['module']for r in rows]
    fresh=[];reused=[];clients=[];all_reports={};warning_rows=[];copy=[]
    def addcopy(p,destination):
        p=Path(p);assert p.is_file();copy.append({'source':str(p),'destination':destination,'sha256':sha(p),'bytes':p.stat().st_size})
    for row in rows:
        m=row['module'];rec=done[m];workspace=B/'workspace'/(m.replace('.','/')+'.lean');obj=B/'objects'/(m.replace('.','/')+'.olean')
        assert sha(row['source'])==sha(workspace)==row['source_sha256']==rec['source_sha256'] and imports(workspace)==row['imports']
        assert rec['dependencies']=={d:done[d]['object_sha256']for d in row['imports']if d!='Init'}
        assert sha(obj)==rec['object_sha256'];actual=policy(row,rec);all_reports[m]=actual
        if m in old:assert row['expected_reports']==profiles(Path(old[m]['log']).read_text())
        canonical=[R/r/(m.replace('.','/')+'.lean')for r in ROOTS if(R/r/(m.replace('.','/')+'.lean')).is_file()]
        if canonical:assert len(canonical)==1 and canonical[0]==Path(row['source'])
        else:
            clients.append(m);assert row['warnings_forbidden'] and Path(rec['log']).read_text().count('warning:')==0
            if m in old:assert row['source_sha256']==oldrows[m]['source_sha256']
        text=Path(rec['log']).read_text();messages=[line.split('warning:',1)[1].strip()for line in text.splitlines()if'warning:'in line]
        assert len(messages)==rec.get('warnings',len(messages))
        if messages:
            oldtext=Path(old[m]['log']).read_text()if m in old else ''
            warning_rows.append({'module':m,'origin':rec['origin'],'occurrences':len(messages),'messages':messages,'prior_same_module_message_present':[message in oldtext for message in messages],'prior_log_sha256':old[m]['log_sha256']if m in old else None,'log_sha256':rec['log_sha256'],'comparison_scope':'Exact warning headline text, independent of changed paths/line numbers; no claim about explanatory continuation formatting.'})
        if rec['origin']=='candidate_fresh':
            fresh.append(m);assert m in forced and obj.is_file() and not obj.is_symlink()
            rawpath=Path(rec['log']).with_name('record.json');assert read(rawpath)==rec
            assert sha(rec['source'])==row['source_sha256'] and rec['candidate']==row['source']
            assert rec['command']==[str(LEAN),'-j1','-M12288','--root='+str(B/'workspace'),'-o',str(obj),str(workspace)]
            assert rec['timeout_seconds']==(900 if 'KSites215Batch'in m or('KSource215FwdCheck'in m and m not in initial)else 120) and rec['memory_mebibytes']==12288
            assert rec['compiler_sha256']==LEAN_SHA and rec['helper_sha256']==SUPERVISOR_SHA
            assert rec['exit_code']==0 and not rec['timed_out']
            assert rec['reports']==actual
            attempt=rawpath.parent;assert sha(attempt/workspace.name)==row['source_sha256']
            addcopy(rawpath,'actual/attempts/'+attempt.name+'/record.json');addcopy(rec['log'],'actual/attempts/'+attempt.name+'/compiler.log')
            addcopy(attempt/workspace.name,'actual/attempts/'+attempt.name+'/'+workspace.name)
        else:
            reused.append(m);assert m not in forced and rec=={**old[m],'origin':oldorigin[m]}
            prior=Path(coverage[m]['basis'])/'objects'/(m.replace('.','/')+'.olean')
            assert obj.is_symlink() and obj.resolve(strict=True)==prior.resolve(strict=True)
        addcopy(workspace,'sources/'+m.replace('.','/')+'.lean')
    assert len(fresh)==107 and set(fresh)==forced and len(reused)==107
    assert result['fresh_modules']==fresh and result['reused_modules']==reused
    assert len(clients)==15 and 'MacroSharing18Api'in clients and 'MacroNamespace18Probe'not in selected
    old_clients={m for m in old if not m.startswith(('BusyBeaver.','FirstOrder.','ZF.','BoundedZFCConsistency.'))}
    assert len(old_clients)==14 and sum(len(all_reports[m])for m in old_clients)==83
    assert sum(len(all_reports[m])for m in ['WFModelCompat12','ZFNativeCompat12'])==10
    assert len(all_reports['BusyBeaver.ZFC.WFTheory'])==5
    new_profiles={m:all_reports[m]for m in selected if m not in old}
    assert new_profiles==result['new_module_actual_profiles'] and set(new_profiles)=={'MacroSharing18Api'} and len(new_profiles['MacroSharing18Api'])==10
    client_reference=read('/tmp/k215-phase18-clients/client-checked-v3-map.json')['required']
    assert selected['MacroSharing18Api']['source_sha256']==client_reference['source_sha256'] and new_profiles['MacroSharing18Api']==client_reference['expected_reports']
    baseline_record=read('/tmp/k215-phase18-clients/baseline-run3/MacroSharing18Api/record.json')
    assert baseline_record['status']=='PASS' and baseline_record['exit_code']==0 and not baseline_record['timed_out'] and baseline_record['warnings']==0
    assert baseline_record['source_sha256']==sha(baseline_record['source'])==client_reference['source_sha256'] and sha(baseline_record['log'])==baseline_record['log_sha256']
    assert profiles(Path(baseline_record['log']).read_text())==new_profiles['MacroSharing18Api']
    assert all(old[m]['object_sha256']==h for m,h in baseline_record['dependencies'].items())
    audit_reports=[]
    assert len(result['audits'])==len(plan['audits'])==2
    for row,rec in zip(plan['audits'],result['audits']):
        m=row['module'];directory=B/('audit-'+m);source=directory/(m+'.lean');obj=directory/(m+'.olean');raw=directory/'record.json'
        assert rec['module']==m and read(raw)==rec and sha(row['source'])==sha(source)==row['source_sha256']==rec['source_sha256']
        assert rec['command']==[str(LEAN),'-j1','-M12288','--root='+str(directory),'-o',str(obj),str(source)]
        assert rec['dependencies']=={n:r['object_sha256']for n,r in done.items()} and sha(obj)==rec['object_sha256']
        assert rec['timeout_seconds']==120 and rec['memory_mebibytes']==12288 and rec['compiler_sha256']==LEAN_SHA and rec['helper_sha256']==SUPERVISOR_SHA
        assert rec['origin']=='candidate_fresh_audit' and rec['warnings']==0 and rec['exit_code']==0 and not rec['timed_out']
        actual=policy(row,rec);assert rec['reports']==actual;audit_reports.extend(actual)
        for p in [raw,Path(rec['log']),source]:addcopy(p,'actual/audit-'+m+'/'+p.name)
    assert len(audit_reports)==10
    # Independently enumerate only the finite literal program table's decoder leaves.
    # This is static source binding, not TM execution or a rerun of a supplied generator.
    program=Path(selected['BusyBeaver.ZFC.KSource215Program']['source']).read_text();nodes={}
    edge=r'\(?\.(node|inc|decnz|brk|cont|halt)(?:\s+(\d+))?\)?'
    for match in re.finditer(r'(?m)^\s*\| (\d+) => \('+edge+r', '+edge+r'\)\s*$',program):
        n,a,ai,b,bi=match.groups();assert int(n)not in nodes;nodes[int(n)]=[(a,int(ai)if ai else 0),(b,int(bi)if bi else 0)]
    assert set(nodes)==set(range(179)) and re.search(r'def p215 : Program := ⟨p215Nodes, 178, 179⟩',program)
    assert 'def t215 : Tree := ptree p215'in program and 'theorem t215_eq : ptree p215 = t215 := by rfl'in program
    leafcodes={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'};leaves=[]
    def walk(n,fuel,prefix):
        assert fuel>0
        for bit,(kind,arg)in zip('01',nodes[n]):
            path=prefix+bit
            if kind=='node':walk(arg,fuel-1,path)
            else:leaves.append([path,leafcodes[kind],None if kind=='halt'else arg])
    assert 'def ptree (p : Program) : Tree := toTree p (p.nnodes + 1) p.root' in Path(selected['BusyBeaver.ZFC.RMBisim']['source']).read_text()
    walk(178,180,'')
    original=R/'Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json';assert leaves==read(original) and len(leaves)==4751
    kinds=Counter(row[1]for row in leaves);assert dict(kinds)=={'CD':1425,'CB':98,'CI':1900,'CC':1327,'CH':1}
    assert sum(2 if row[1]=='CD'else 1 for row in leaves)==6176
    blocks={};site_modules=['BusyBeaver.ZFC.KSites215Batch'+str(i).zfill(3)for i in range(9)]
    for m in site_modules:
        assert m in fresh and selected[m]['source_sha256']==oldrows[m]['source_sha256']
        text=Path(selected[m]['source']).read_text();pattern=r'theorem block_(\d+)\s*:\s*allSites \(KSim.checkEdge tm215\) \[([^]]*)\]\s*\(descend KSource215.t215 \[([^]]*)\]\) = true := by\s*exact KFastSites215.allSites_of_fast \(by decide \+kernel\)'
        matches=list(re.finditer(pattern,text));assert len(matches)==len(re.findall(r'(?m)^theorem block_',text))
        for match in matches:
            num,rev,forward=match.groups();num=int(num);assert num not in blocks
            bits=lambda s:[x.strip()for x in s.split(',')if x.strip()]
            assert bits(rev)==list(reversed(bits(forward))) and set(bits(forward))<={'true','false'}
            blocks[num]=''.join('1'if x=='true'else'0'for x in bits(forward))
    assert set(blocks)==set(range(105))
    for prefix in blocks.values():assert any(row[0].startswith(prefix)for row in leaves)
    assert all(sum(path.startswith(prefix)for prefix in blocks.values())==1 for path,_,_ in leaves)
    root=Path(selected['BusyBeaver.ZFC.KSites215']['source']).read_text();assert selected['BusyBeaver.ZFC.KSites215']['source_sha256']==oldrows['BusyBeaver.ZFC.KSites215']['source_sha256']
    assert sorted(map(int,re.findall(r'\bblock_(\d+)\b',root)))==list(range(105))
    assert 'theorem all_sites : allSites (KSim.checkEdge tm215) [] KSource215.t215 = true :='in root
    assert 'KSim.covered_of_allSites tm215 KSource215.p215 KSource215.t215 KSource215.t215_eq all_sites'in root
    endpoint=set()
    def ep(m):
        if m=='Init'or m in endpoint:return
        endpoint.add(m)
        for d in selected[m]['imports']:ep(d)
    ep('BusyBeaver.ZFC.KEndpoint215')
    assert len(endpoint)==178 and sum(Path(selected[m]['source']).stat().st_size for m in endpoint)==1767300
    assert len(plan['present_inputs'])==39 and len(plan['absent_inputs'])==8 and len(before['inputs'])==1084
    for p,h in plan['present_inputs'].items():assert sha(p)==h and before['inputs'][p]==h
    for p,h in before['inputs'].items():assert sha(p)==h,p
    assert before['absent_inputs']==plan['absent_inputs']
    for p in plan['absent_inputs']:assert not Path(p).exists() and not Path(p).is_symlink()
    for m in plan['retired_modules']:
        assert m not in selected;p=B/'objects'/(m.replace('.','/')+'.olean');assert not p.exists() and not p.is_symlink()
    first=(O/'build.stdout').read_text();middle=(IO/'resume.stdout').read_text();stdout=(C/'resume2.stdout').read_text()
    checks=lambda text:re.findall(r'(?m)^CHECK (\S+)$',text)
    passes=lambda text:re.findall(r'(?m)^PASS (\S+) ',text)
    reuse_names=lambda text:re.findall(r'(?m)^REUSE (\S+) ',text)
    first_checks,middle_checks,last_checks=map(checks,[first,middle,stdout])
    assert len(first_checks)==19 and len(middle_checks)==52 and len(last_checks)==38
    assert first_checks[:-1]+middle_checks[:-1]+last_checks==fresh
    assert passes(first)==first_checks[:-1] and passes(middle)==middle_checks[:-1] and passes(stdout)==last_checks
    first_reuses,middle_reuses,last_reuses=map(reuse_names,[first,middle,stdout])
    assert (len(first_reuses),len(middle_reuses),len(last_reuses))==(5,79,23)
    assert first_reuses+middle_reuses+last_reuses==reused
    assert middle_checks[-1]=='BusyBeaver.ZFC.KSites215Batch002' and last_checks[0]==middle_checks[-1]
    assert re.findall(r'(?m)^AUDIT (\S+)$',stdout)==[r['module']for r in plan['audits']]
    assert not re.search(r'(?m)^(?:FAIL|AUDIT)\b',middle) and not middle.rstrip().endswith('audits')
    assert all(done[m]==rec for m,rec in initial.items()) and all(done[m]==rec for m,rec in retained.items())
    attempts=list((B/'attempts').iterdir());assert len(attempts)==109 and {int(p.name.split('-',1)[0])for p in attempts}==set(range(1,110))
    excluded={'019-BusyBeaver.ZFC.KSource215FwdCheck12','071-BusyBeaver.ZFC.KSites215Batch002'}
    assert {str(Path(done[m]['log']).parent)for m in fresh}=={str(p)for p in attempts if p.name not in excluded}
    assert stdout.rstrip().endswith('COMPLETE 214 2 audits') and not re.search(r'(?m)^FAIL\b',stdout)
    for p in [C/'build-forward-budget.py',C/'plan.json',C/'resume2-freeze.json',args.outer,C/'resume2.stdout',C/'resume2.stderr',B/'result.json',B/'before.json',B/'inventory.json',B/'completed.json',B/'toolchain.json']:
        addcopy(p,'actual/'+p.name)
    destinations=[r['destination']for r in copy];assert len(destinations)==len(set(destinations))
    assert len(copy)==214+107*3+2*3+11==552
    old_projects=set(old)-old_clients;assert len(old_projects)==199
    old_bytes=sum((BASIS[0][0]/'workspace'/(m.replace('.','/')+'.lean')).stat().st_size for m in old_projects)
    new_bytes=sum(Path(selected[m]['source']).stat().st_size for m in old_projects)
    lines_removed=sum(len((BASIS[0][0]/'workspace'/(m.replace('.','/')+'.lean')).read_text().splitlines())-len(Path(selected[m]['source']).read_text().splitlines())for m in old_projects)
    assert (old_bytes,new_bytes,old_bytes-new_bytes,lines_removed)==(2084576,2057203,27373,683)
    adoption=read('/tmp/k215-phase18-integration/source-adoption.json');producer=Path(adoption['retired_producer']['snapshot'])
    assert sha(producer)==adoption['retired_producer']['before_sha256'] and producer.stat().st_size==3806 and len(producer.read_text().splitlines())==74
    assert not(R/adoption['retired_producer']['path']).exists()
    review={'status':'PASS_READ_ONLY_ACTUAL_EVIDENCE_REVIEW','runner_sha256':RUNNER_SHA,'plan_sha256':PLAN_SHA,'outer_sha256':sha(args.outer),'resource_transition_sha256':sha(T/'transition.json'),'resource_resume_freeze_sha256':sha(C/'resume-freeze.json'),'original_failed_outer_sha256':sha(O/'build-outer.json'),'retained_providers':23,'retained_fresh':18,'retained_reuses':5,'first_resume_fresh_successes':51,'first_resume_reuses':79,'detached_resume_fresh_invocations':38,'detached_resume_reuses':23,'retained_before_detached':153,'provider_compiler_invocations':109,'interrupted_executor_exit_code':143,'interrupted_compiler_exit_known':False,'partial_attempt071_excluded':True,'partial_physical_object_was_unaccepted':True,'interruption_sha256':sha(I/'interruption.json'),'detached_resume_freeze_sha256':sha(C/'resume2-freeze.json'),'interruption_history_files':len(interruption_context),'failed_attempt_preserved':True,'resource_only_successor':True,'resource_history_files':len(resource_history),'result_sha256':sha(B/'result.json'),'provider_count':214,'project_modules':199,'typed_clients':15,'changed_sources':15,'fresh_providers':107,'source_transitive_reuses':107,'endpoint_project_modules':178,'endpoint_source_bytes':1767300,'all_old_client_reports':83,'new_macro_client_reports':10,'compatibility_client_reports':10,'WFTheory_reports':5,'fresh_endpoint_audit_reports':audit_reports,'new_exact_profiles':new_profiles,'site_batches':9,'site_blocks':105,'site_leaves':4751,'site_outcomes':6176,'site_edge_kinds':dict(kinds),'site_scope':'Fresh kernel checks of all nine batches plus root coverage; original pinned site list exactly equals statically enumerated literal program decoder leaves.','historical_raw_present':179,'historical_raw_absent_inherited':34,'historical_raw_missing_object_hash':missing_raw_object_hash,'historical_raw_scope':RAW_SCOPE,'additional_pins_postchecked':39,'absences_postchecked':8,'owner_inputs_postchecked':1084,'warning_occurrences':sum(r['occurrences']for r in warning_rows),'fresh_warning_occurrences':sum(r['occurrences']for r in warning_rows if r['origin']=='candidate_fresh'),'all_fresh_warning_headlines_preexisted':all(all(r['prior_same_module_message_present'])for r in warning_rows if r['origin']=='candidate_fresh'),'warnings':warning_rows,'client_and_audit_warnings':0,'copy_plan_files':len(copy),'objects_copied':False,'helper_sha256':sha(__file__),'project_bytes_removed':27373,'lean_lines_removed':683,'producer_bytes_removed':3806,'producer_lines_removed':74,'scope':'Frozen combined215 closure and required15typedclients only. Optional qualified-record-namespace probe is excluded; its failure remains separate context. No variant217–225 full-stack claim.'}
    save(args.out,review);save(args.out.with_name('publication-copy-plan.json'),{'status':'DRAFT_COPY_PLAN_NO_MUTATION','files':copy,'additional_resource_history':resource_history,'additional_interruption_history':interruption_context,'scope':'Selected actual sources, fresh invocation source/log/record evidence, audits and small metadata; no object files, supplied-code execution, or new archive reader.'});print(json.dumps(review,indent=2))

if __name__=='__main__':main()
