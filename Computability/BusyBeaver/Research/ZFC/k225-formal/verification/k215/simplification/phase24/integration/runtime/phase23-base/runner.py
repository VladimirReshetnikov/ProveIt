#!/usr/bin/env python3
"""DRAFT: one serial, frozen-map phase23 source-transitive kernel check.

Owned draft for root review. Not executed. The map names every selected source,
all audit profiles, exact current bindings, retirements, producer and machine pins.
Historical source bindings come from accepted baseline workspace snapshots.
"""
from pathlib import Path
import argparse, fcntl, hashlib, importlib.util, json, os, re, signal

REPO=Path('/home/codex/.codex/worktrees/ec20/Proofs')
BASIS=[(Path('/tmp/k215-phase22-check-v3/candidate-build-run1'), 'phase22_checked', 226,
        'cd966bd654b04a3c2becbafc00ba1f13f2866fcbab64b5b6715cf6449461dc66')]
SUPERVISOR=REPO/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py'
SUPERVISOR_SHA='a3cf7cc38004bca5e2a2df10c607fe5353896c0454069b4ff24d6b5176c32fbd'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
LEAN_SHA='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
LOCK=Path('/tmp/proveit-k215-proof-build.lock')
STD={'propext','Classical.choice','Quot.sound'}
PATTERN=r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)"

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def save(p,x):
    tmp=p.with_suffix(p.suffix+'.tmp');tmp.write_text(json.dumps(x,indent=2)+'\n');os.replace(tmp,p)
def profiles(text):return [[n,sorted({a.strip() for a in axioms.split(',') if a.strip()})] for n,axioms in re.findall(PATTERN,text)]
def norm(rows):return [[n,sorted(axioms)]for n,axioms in rows]
def terminate(*_):raise KeyboardInterrupt('SIGTERM')
signal.signal(signal.SIGTERM,terminate)
parser=argparse.ArgumentParser();parser.add_argument('--map',type=Path,required=True);parser.add_argument('--out',type=Path,required=True);parser.add_argument('--check-plan',action='store_true');args=parser.parse_args()
assert sha(SUPERVISOR)==SUPERVISOR_SHA and sha(LEAN)==LEAN_SHA
spec=importlib.util.spec_from_file_location('phase23_owned_supervisor',SUPERVISOR)
supervisor=importlib.util.module_from_spec(spec);spec.loader.exec_module(supervisor)
plan=read(args.map)
for path,pin in P23_RUNTIME_INPUTS.items():assert plan['present_inputs'][path]==pin==sha(path)
out=args.out.resolve();out.mkdir(exist_ok=True)
with (out/'output.lock').open('a') as output_lock:
    fcntl.flock(output_lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    inputs={str(p):sha(p)for p in [Path(__file__).resolve(),args.map.resolve(),SUPERVISOR,LEAN]}
    historical={};historical_entries={};basis_objects={};toolchain=None;raw_coverage={}
    for directory,origin,count,pin in BASIS:
        assert sha(directory/'result.json')==pin
        result=read(directory/'result.json');inventory=read(directory/'inventory.json');done=read(directory/'completed.json')
        assert result['status']=='PASS'
        assert sha(directory/'inventory.json')==result['inventory_sha256'] and sha(directory/'completed.json')==result['completed_sha256']
        assert len(done)==len(inventory['modules'])==count
        assert len({r['module']for r in inventory['modules']})==count
        this_toolchain=read(directory/'toolchain.json')
        if toolchain is None:toolchain=this_toolchain
        else:assert this_toolchain==toolchain
        for name in ['result.json','inventory.json','completed.json','toolchain.json']:
            inputs[str(directory/name)]=sha(directory/name)
        entries={r['module']:r for r in inventory['modules']}
        for m,rec in done.items():
            row=entries[m];source=directory/'workspace'/(m.replace('.','/')+'.lean')
            obj=directory/'objects'/(m.replace('.','/')+'.olean')
            assert sha(source)==row['source_sha256']==rec['source_sha256'],m
            assert rec['status']=='PASS' and rec.get('exit_code',0)==0 and not rec.get('timed_out',False)
            assert rec['dependencies']=={d:done[d]['object_sha256']for d in row['imports'] if d!='Init'}
            assert sha(obj)==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256']
            assert 'error:' not in Path(rec['log']).read_text() and 'sorryAx' not in Path(rec['log']).read_text()
            assert all(set(ax)<=STD for _,ax in profiles(Path(rec['log']).read_text()))
            if 'command' in rec:
                assert rec['command'][0:3]==[str(LEAN),'-j1','-M12288'] and rec['command'][-1]==rec['source']
                # Accepted old commands can name a later changed canonical source.
                # Historical source bytes are bound above by the accepted baseline workspace.
            raw_path=Path(rec['log']).with_name('record.json')
            raw=None
            if raw_path.is_file():
                raw=read(raw_path)
                for key in ['module','source_sha256','dependencies','log_sha256','status']:
                    assert raw[key]==rec[key],(m,key)
                if 'object_sha256' in raw:assert raw['object_sha256']==rec['object_sha256'],m
                for key in ['command','exit_code','timed_out']:
                    if key in rec:assert raw[key]==rec[key],(m,key)
                assert raw['exit_code']==0 and not raw['timed_out']
                assert raw['command'][0:3]==[str(LEAN),'-j1','-M12288']
                inputs[str(raw_path)]=sha(raw_path)
            raw_coverage[m]={'basis':str(directory),'accepted_source':str(source),'log':rec['log'],'raw_record':str(raw_path)if raw is not None else None,'raw_has_object_hash':bool(raw is not None and 'object_sha256'in raw),'scope':'Pinned accepted baseline aggregate, workspace source, object and log; adjacent original raw record additionally checked when present.'}
            if m in historical:
                assert row['source_sha256']==historical_entries[m]['source_sha256'] and row['imports']==historical_entries[m]['imports']
                assert rec['object_sha256']==historical[m]['object_sha256']
            historical[m]=rec;historical_entries[m]=row;basis_objects[m]=(obj,origin)
            for p in [source,obj,Path(rec['log'])]:inputs[str(p)]=sha(p)
    assert len(historical)==226
    for key in ['lean','lake','Init.olean','project_toolchain']:
        row=toolchain[key];assert sha(row['path'])==row['sha256'];inputs[row['path']]=row['sha256']
    rows=plan['modules'];selected={r['module']:r for r in rows};assert len(rows)==len(selected)
    assert set(plan['targets'])<=set(selected)
    assert len(rows)==plan['expected']['provider_count']
    retired=set(plan['retired_modules']);assert not retired&set(selected)
    for row in rows:
        source=Path(row['source']);assert sha(source)==row['source_sha256']
        imports=[m for line in re.findall(r'(?m)^\s*(?:public\s+)?import\s+([^\n]+)',supervisor.without_comments_strings(source.read_text()))for m in line.split()]
        assert imports==row['imports']
        assert 'expected_reports' in row and norm(row['expected_reports'])==row['expected_reports']
        inputs[str(source)]=row['source_sha256']
    # Check topology and exact target closure, so dead extra providers cannot hide in the map.
    visited=set();active=set();order=[]
    def visit(m):
        if m=='Init':return
        assert m in selected and m not in retired
        if m in visited:return
        assert m not in active
        active.add(m)
        for d in selected[m]['imports']:visit(d)
        active.remove(m);visited.add(m);order.append(m)
    for target in plan['targets']:visit(target)
    assert order==[r['module']for r in rows]
    changed={m for m,r in selected.items()if m not in historical or(r['source_sha256'],r['imports'])!=(historical_entries[m]['source_sha256'],historical_entries[m]['imports'])}
    forced=set(changed)
    while True:
        more=forced|{m for m,r in selected.items()if set(r['imports'])&forced}
        if more==forced:break
        forced=more
    assert sorted(changed)==plan['expected']['changed_sources']
    assert sorted(forced)==plan['expected']['fresh_by_source_transitivity']
    # Machine, producer, selected-canonical and immutable provenance inputs are separate bindings.
    for path,pin in plan['present_inputs'].items():assert sha(path)==pin;inputs[path]=pin
    absent=plan['absent_inputs'];assert len(absent)==len(set(absent))
    for path in absent:assert not Path(path).exists() and not Path(path).is_symlink()
    for audit in plan['audits']:
        assert sha(audit['source'])==audit['source_sha256'];inputs[audit['source']]=audit['source_sha256']
        assert norm(audit['expected_reports'])==audit['expected_reports']
    owner={'plan_sha256':sha(args.map),'runner_sha256':sha(__file__),'targets':plan['targets'],'inputs':inputs,'absent_inputs':absent,'changed_sources':sorted(changed),'force_basis_rebuild':sorted(forced),'historical_raw_coverage':raw_coverage}
    if args.check_plan:
        assert {p.name for p in out.iterdir()}=={'output.lock'}
        receipt={'status':'PASS_METADATA_PREFLIGHT_NO_COMPILER_EXECUTION','provider_count':len(rows),'old_basis_provider_count':len(historical),'changed_count':len(changed),'fresh_count':len(forced),'reusable_count':len(rows)-len(forced),'audit_count':len(plan['audits']),**owner}
        save(out/'preflight.json',receipt);print(json.dumps(receipt,indent=2),flush=True);raise SystemExit(0)
    cache=out/'objects';workspace=out/'workspace';env=os.environ.copy();env['LEAN_PATH']=str(cache);env['LEAN_NUM_THREADS']='1'
    if (out/'before.json').exists():
        assert read(out/'before.json')==owner;done=read(out/'completed.json')
    else:
        assert {p.name for p in out.iterdir()}=={'output.lock'}
        save(out/'before.json',owner);save(out/'inventory.json',{'modules':rows,'targets':plan['targets'],'external_imports':['Init']});save(out/'toolchain.json',toolchain)
        done={};save(out/'completed.json',done)
    def policy(row,rec):
        if rec['status']!='PASS' or rec.get('exit_code',0)!=0 or rec.get('timed_out',False):return False
        text=Path(rec['log']).read_text()
        if 'error:' in text or 'sorryAx' in text:return False
        actual=profiles(text)
        if not all(set(ax)<=STD for _,ax in actual):return False
        if actual!=row['expected_reports']:return False
        return not row.get('warnings_forbidden',False) or 'warning:' not in text
    def source_path(m):return workspace/(m.replace('.','/')+'.lean')
    for row in rows:
        m=row['module'];source=source_path(m);source.parent.mkdir(parents=True,exist_ok=True);source.write_bytes(Path(row['source']).read_bytes())
        obj=cache/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
        for parent in obj.parents:
            assert not parent.is_symlink()
            if parent==cache:break
        deps={d:done[d]['object_sha256']for d in row['imports']if d!='Init'}
        for d,h in deps.items():assert sha(cache/(d.replace('.','/')+'.olean'))==h
        def usable(rec,path):return policy(row,rec) and rec['source_sha256']==row['source_sha256'] and rec['dependencies']==deps and path.is_file() and sha(path)==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256']
        if m in done and usable(done[m],obj):
            assert done[m]['origin']=='candidate_fresh' or (m not in forced and done[m]['origin']in{'phase22_checked'})
            continue
        if m in historical and m not in forced and usable(historical[m],basis_objects[m][0]):
            prior,origin=basis_objects[m];obj.unlink(missing_ok=True);obj.symlink_to(prior);done[m]={**historical[m],'origin':origin};save(out/'completed.json',done);print('REUSE',m,origin,flush=True)
        else:
            attempts=out/'attempts';attempts.mkdir(exist_ok=True);attempt=attempts/(str(len(list(attempts.iterdir()))+1).zfill(3)+'-'+m);attempt.mkdir()
            (attempt/source.name).write_bytes(source.read_bytes());log=attempt/'compiler.log';record=attempt/'record.json';obj.unlink(missing_ok=True)
            timeout=900 if 'KSites215Batch' in m or 'KSource215FwdCheck' in m else 120
            command=[str(LEAN),'-j1','-M12288','--root='+str(workspace),'-o',str(obj),str(source)]
            rec={'module':m,'source':str(source),'source_sha256':row['source_sha256'],'candidate':row['source'],'dependencies':deps,'command':command,'timeout_seconds':timeout,'memory_mebibytes':12288,'compiler_sha256':LEAN_SHA,'helper_sha256':SUPERVISOR_SHA,'log':str(log),'origin':'candidate_fresh'}
            print('CHECK',m,flush=True);ok=supervisor.run_locked(command,REPO,env,LOCK,log,timeout,rec,record)
            text=log.read_text();rec.update(warnings=text.count('warning:'),reports=profiles(text),object_sha256=sha(obj)if ok else None);save(record,rec)
            if 'expected_reports' in row and profiles(text)!=row['expected_reports']:save(attempt/'assumption-profile-discrepancy.json',{'expected':row['expected_reports'],'actual':profiles(text),'module':m,'policy':'Exact equality. Any changed assumption set requires explicit mathematical review and a new frozen plan.'})
            print(rec['status'],m,round(rec['seconds'],3),rec['warnings'],'warnings',flush=True)
            assert ok and not rec['timed_out'] and policy(row,rec) and 'warning:' not in text,m
            done[m]=rec;save(out/'completed.json',done)
        assert sha(obj)==done[m]['object_sha256']
    def postcheck():
        for p,h in inputs.items():assert sha(p)==h,p
        for p in absent:assert not Path(p).exists() and not Path(p).is_symlink(),p
        for m in retired:
            p=cache/(m.replace('.','/')+'.olean');assert not p.exists() and not p.is_symlink()
        assert set(done)==set(selected)
        for row in rows:
            m=row['module'];rec=done[m];assert sha(row['source'])==sha(source_path(m))==row['source_sha256']==rec['source_sha256']
            assert rec['dependencies']=={d:done[d]['object_sha256']for d in row['imports']if d!='Init'}
            assert sha(cache/(m.replace('.','/')+'.olean'))==rec['object_sha256'] and sha(rec['log'])==rec['log_sha256'] and policy(row,rec)
    postcheck();audits=[]
    for row in plan['audits']:
        m=row['module'];directory=out/('audit-'+m);directory.mkdir();source=directory/(m+'.lean');source.write_bytes(Path(row['source']).read_bytes())
        obj=directory/(m+'.olean');log=directory/'compiler.log';record=directory/'record.json'
        command=[str(LEAN),'-j1','-M12288','--root='+str(directory),'-o',str(obj),str(source)]
        rec={'module':m,'source':str(source),'source_sha256':row['source_sha256'],'dependencies':{n:r['object_sha256']for n,r in done.items()},'command':command,'timeout_seconds':120,'memory_mebibytes':12288,'compiler_sha256':LEAN_SHA,'helper_sha256':SUPERVISOR_SHA,'log':str(log),'origin':'candidate_fresh_audit'}
        print('AUDIT',m,flush=True);ok=supervisor.run_locked(command,REPO,env,LOCK,log,120,rec,record)
        text=log.read_text();rec.update(warnings=text.count('warning:'),reports=profiles(text),object_sha256=sha(obj)if ok else None);save(record,rec)
        if profiles(text)!=row['expected_reports']:save(directory/'assumption-profile-discrepancy.json',{'expected':row['expected_reports'],'actual':profiles(text),'module':m})
        assert ok and policy(row,rec) and 'warning:' not in text and sha(source)==row['source_sha256'];audits.append(rec)
    postcheck()
    for rec in audits:assert sha(rec['source'])==rec['source_sha256'] and sha(rec['log'])==rec['log_sha256'] and sha(Path(rec['source']).with_suffix('.olean'))==rec['object_sha256']
    save(out/'result.json',{'status':'PASS','targets':plan['targets'],'provider_count':len(done),'changed_sources':sorted(changed),'force_basis_rebuild':sorted(forced),'fresh_modules':[m for m,r in done.items()if r['origin']=='candidate_fresh'],'reused_modules':[m for m,r in done.items()if r['origin']!='candidate_fresh'],'audits':audits,'basis_result_sha256':BASIS[0][3],'source_transitive_reuse_only':True,'all_source_object_dependency_log_toolchain_inputs_postchecked':True,'new_module_actual_profiles':{m:profiles(Path(done[m]['log']).read_text())for m in selected if m not in historical},'historical_raw_coverage':raw_coverage,'inventory_sha256':sha(out/'inventory.json'),'completed_sha256':sha(out/'completed.json'),'runner_sha256':sha(__file__),'map_sha256':sha(args.map),'scope':'One exact frozen selected closure and explicitly named typed clients/audits. No inference for other variant certificate stacks.'})
    print('COMPLETE',len(done),len(audits),'audits',flush=True)
