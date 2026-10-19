#!/usr/bin/env python3
"""Strict serial Rotation240 full coverage; each pair receives a separate shared120s budget."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-rotation240-coverage-production')
MANIFEST_SHA='53a200514bb07119e61e7aeddc7366d39700490d801e86ba5177110a95623dc2'
STANDARD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rel=lambda m,s='.olean':Path(m.replace('.','/')).with_suffix(s)
imports=lambda p:re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def require(x,msg):
    if not x:raise RuntimeError(msg)
def reports(text):
    rr=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in rr]
def run_unit(a):
    require(__debug__,'No optimized Python.')
    W=a.output.resolve();require(not W.exists()or(W.is_dir()and not any(W.iterdir())),'Fresh output required.')
    require(not W.is_relative_to(Path('/home/codex/.codex/worktrees/ec20/Proofs')) and not W.is_relative_to(Path('/home/codex/src/Proofs')),'External output only.')
    tracked={}
    def pin(p,h):
        p=Path(p).resolve();require(p.is_file()and sha(p)==h,'Changed input '+str(p))
        require(str(p)not in tracked or tracked[str(p)]==h,'Conflicting identity.');tracked[str(p)]=h;return p
    M=pin(a.manifest,MANIFEST_SHA);pin(__file__,sha(__file__));b=json.loads(M.read_text());u=b['units'][a.unit]
    for x in [b['generation'],b['author_metadata_source'],*b['additional_inputs']]:pin(x['path'],x['sha256'])
    MODULE=u['module'];PROBES=u['qualified_probes'];S=pin(u['source']['path'],u['source']['sha256']);A=pin(u['audit']['path'],u['audit']['sha256'])
    SOURCE_SHA=u['source']['sha256'];AUDIT_SHA=u['audit']['sha256']
    require(imports(S)==u['imports']and imports(A)==[MODULE],'Imports changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==PROBES and len(PROBES)==u['probes'],'Audit names changed.')
    require(len(re.findall(r'^example\b',A.read_text(),re.M))==u['callers'],'Typed callers changed.')
    for q in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text()),'Untrusted proof exit.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text()),'Raised proof limits.')
    supplied={}
    for name,path,h in a.parent:
        require(name not in supplied and re.fullmatch('[0-9a-f]{64}',h),'Duplicate or malformed predecessor.');supplied[name]=dict(path=str(Path(path).resolve()),sha256=h)
    require(set(supplied)==set(u['future_parents']),'Exactly the required actual predecessors must be supplied.')
    requested=[]
    for name in u['anchors']:requested.append((name,b['anchors'][name]['record'],b['anchors'][name]))
    for name in u['future_parents']:
        spec=b['units'][name];requested.append((name,supplied[name],dict(module=spec['module'],source_sha256=spec['source']['sha256'],audit_sha256=spec['audit']['sha256'],probes=spec['probes'],callers=spec['callers'],schema='modern')))
    C=pin(b['compiler']['path'],b['compiler']['sha256']);pool={};toolpool={};evidence=[];summaries=[]
    def add(q,evidence_path):
        if q['module']not in b['all_allowed_projects']:return
        z={k:q[k]for k in ['module','source','source_sha256','object','object_sha256']};z['evidence']=str(evidence_path)
        for k in ['source','object']:pin(z[k],z[k+'_sha256'])
        if z['module']in pool:
            v=pool[z['module']];require((v['source_sha256'],v['object_sha256'],Path(v['object']).resolve())==(z['source_sha256'],z['object_sha256'],Path(z['object']).resolve()),'Conflicting provider '+z['module'])
        else:pool[z['module']]=z
    for name,descriptor,expected in requested:
        E=pin(descriptor['path'],descriptor['sha256']);e=json.loads(E.read_text());evidence.append(dict(path=str(E),sha256=descriptor['sha256']))
        require(e['status']=='PASS'and not e['prepare_only']and(e['named_axiom_probes'],e['callers'])==(expected['probes'],expected['callers']),'Incomplete or wrong predecessor '+name)
        require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete predecessor evidence.')
        warnings=e['warnings'];require((sum(warnings.values())if isinstance(warnings,dict)else warnings)==0,'Predecessor has warnings.')
        require(e['compiler']['sha256']==b['compiler']['sha256']and Path(e['compiler']['path']).resolve()==C,'Different compiler.')
        require(not e['dependency_build']and not e['downloads']and not e.get('compiler_version_query_performed',e['compiler'].get('compiler_version_query_performed',False)),'Wrong predecessor execution scope.')
        if expected['schema']=='legacy_runtime245':
            require(name=='generic'and(e['shared_wall_seconds'],e['per_command_timeout_seconds'])==(120,120),'Wrong pinned legacy schema.')
        else:require((e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[]),'Changed predecessor limits.')
        for path,h in e['before'].items():pin(path,h)
        for role in ['source','audit']:
            require(e[role]['sha256']==expected[role+'_sha256'],'Wrong predecessor source/audit.')
            for key in ['path','snapshot']:pin(e[role][key],e[role]['sha256'])
        require([q['label']for q in e['commands']]==['source','audit'],'Wrong predecessor commands.')
        for command in e['commands']:
            require(command['exit_code']==0 and not command.get('timed_out',False)and command.get('interrupted')is None,'Predecessor command failure.')
            argv=command['command'];require(argv[:3]==[str(C),'-j1','-M4096']and argv[-1]==e[command['label']]['snapshot'],'Changed predecessor argv.')
            require(len(argv)==(7 if command['label']=='source'else 5)and argv[3].startswith('--root='),'Extra predecessor options.')
            log=Path(command['log'])if 'log'in command else E.parent/(command['label']+'.log');require(log.read_text()==command['output'],'Changed raw predecessor log.')
            pin(log,command.get('log_sha256',sha(log)))
            require('error:'not in command['output']and'warning:'not in command['output']and'sorryAx'not in command['output'],'Unexpected predecessor diagnostic.')
        ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        require(len(ns)==expected['probes']and[q['name']for q in rr]==ns and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong predecessor axiom reports.')
        fs=e['fresh_modules'];require(len(fs)==1 and fs[0]['module']==expected['module'],'Wrong fresh predecessor module.');f=fs[0]
        require(f['source_sha256']==e['source']['sha256']and e['source_object_recorded_before_audit'],'Wrong fresh source capture.');pin(f['path'],f['sha256'])
        require(all(e['source_pass_object'][k]==f[k]for k in ['module','path','sha256','source_sha256']),'Missing pre-audit object.')
        cap=e['fresh_first_provider_before_audit'];require(cap['module']==f['module']and Path(cap.get('path',cap.get('actual_first'))).resolve()==Path(f['path']).resolve()and cap['sha256']==f['sha256'],'Wrong fresh first provider.')
        first={q['module']:q for q in e['actual_first_providers']}
        for q in e['reused_modules']:
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==q[k+'_sha256'],'Unbound predecessor pair.')
            old=first[q['module']];require(Path(old.get('resolved',old['actual_first'])).resolve()==Path(q['object']).resolve()and old['sha256']==q['object_sha256'],'Wrong historical first provider.')
            add(q,E)
        add(dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256']),E)
        for q in e['toolchain_providers']:
            pp=pin(q['object'],q['object_sha256']);require(pp==C.parent.parent/'lib/lean'/rel(q['module'])and e['before'].get(str(pp))==q['object_sha256'],'Wrong predecessor tool.')
            if q['module']in toolpool:require(toolpool[q['module']]['object_sha256']==q['object_sha256'],'Conflicting tool.')
            else:toolpool[q['module']]={k:q[k]for k in ['module','object','object_sha256']}
        summaries.append(dict(name=name,verification=evidence[-1],schema=expected['schema'],module=f['module'],source_sha256=f['source_sha256'],fresh_object_sha256=f['sha256'],all_current_parent_inputs_rehashed=True))
    seen=set();toolnames={'Init'}
    def visit(m):
        if m in {'Init','Lean.Elab.Tactic.Omega'}:toolnames.add(m);return
        require(m in pool,'Unselected import '+m)
        if m in seen:return
        seen.add(m)
        for n in imports(pool[m]['source']):visit(n)
    for m in imports(S):visit(m)
    require(seen==set(u['expected_projects'])and toolnames==set(u['expected_tools']),'Wrong exact DFS.')
    reused=[pool[m]for m in sorted(seen)];tools=[toolpool[m]for m in sorted(toolnames)]
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    for q in reused:
        dest=cache/rel(q['module']);dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
    ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss);aa=snaps/'Audit.lean';shutil.copyfile(A,aa)
    pin(ss,SOURCE_SHA);pin(aa,AUDIT_SHA);toolroot=C.parent.parent/'lib/lean'
    def first(m):return next((r/rel(m)).resolve()for r in [cache,toolroot]if(r/rel(m)).is_file())
    def providers():
        rows=[]
        for q in reused+tools:
            pp=first(q['module']);require(pp==Path(q['object']).resolve()and sha(pp)==q['object_sha256'],'Wrong actual provider.')
            rows.append(dict(module=q['module'],actual_first=str(pp),sha256=sha(pp)))
        return rows
    actual=providers();env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1')
    r=dict(status='PREPARED_NOT_BUILT',prepare_only=True,unit=a.unit,scope=b['scope'],source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),manifest=dict(path=str(M),sha256=MANIFEST_SHA),provider_evidence=evidence,parent_summaries=summaries,compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,toolchain_providers=tools,actual_first_providers=actual,exact_project_import_closure=sorted(seen),exact_project_prerequisite_count=len(reused),before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False)
    def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
    def post():
        r['after']={p:sha(p)for p in tracked};require(r['before']==r['after']and providers()==actual,'Postcheck failed.')
        for q in r['fresh_modules']:require(first(q['module'])==Path(q['path']).resolve()and sha(q['path'])==q['sha256'],'Fresh object changed.')
        r['all_input_provider_postchecks']=True
    save()
    try:
        post();save()
        preparation=W/'preparation.json';preparation.write_text(json.dumps(r,indent=2)+'\n')
        if a.prepare_only:print(W/'verification.json');return
        r.update(status='RUNNING',prepare_only=False,preparation=dict(path=str(preparation),sha256=sha(preparation)));save()
        deadline=time.monotonic()+120
        def run(label,file,obj=None):
            remaining=deadline-time.monotonic();require(remaining>0,'Shared deadline exhausted.')
            cmd=[str(C),'-j1','-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)]
            start=time.monotonic();proc=subprocess.Popen(cmd,cwd=snaps,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
            timeout=False;interrupted=None
            try:data,_=proc.communicate(timeout=remaining)
            except BaseException as ex:
                timeout=isinstance(ex,subprocess.TimeoutExpired);interrupted=None if timeout else type(ex).__name__
                try:os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                data,_=proc.communicate()
            out=data.decode(errors='replace');log=W/(label+'.log');log.write_text(out)
            r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-start,exit_code=proc.returncode,timed_out=timeout,interrupted=interrupted,output=out,log=str(log),log_sha256=sha(log)));save()
            require(not timeout and interrupted is None and proc.returncode==0,'Source/audit failed; output retained.')
            require('sorryAx'not in out and "declaration uses 'sorry'"not in out,'Untrusted output.');return out
        obj=cache/rel(MODULE);require(not obj.exists(),'Target already exists.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)
        q=dict(module=MODULE,path=str(obj),sha256=sha(obj),source_sha256=SOURCE_SHA)
        r.update(fresh_modules=[q],source_pass_object=dict(q,source_command_index=0),source_object_recorded_before_audit=True,fresh_first_provider_before_audit=dict(module=MODULE,path=str(first(MODULE)),sha256=sha(first(MODULE))))
        require(first(MODULE)==obj.resolve(),'Fresh first provider mismatch.');save()
        out=run('audit',aa);rr=reports(out);require([q['name']for q in rr]==PROBES and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong actual reports.')
        post();require(sha(preparation)==r['preparation']['sha256'],'Preparation receipt changed.');r.update(status='PASS',named_axiom_probes=u['probes'],callers=u['callers'],axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')

def descriptor(p):return dict(path=str(Path(p).resolve()),sha256=sha(p))
def successful(b,module,ref):
    """Validate every accepted prior record, without executing any supplied code."""
    p=Path(ref['path']).resolve();require(sha(p)==ref['sha256'],'Changed prior record.')
    d=json.loads(p.read_text());u=b['units'][module]
    require(d['status']=='PASS'and d['prepare_only'] is False and d['before']==d['after']and d['warnings']==0,'Prior is not a zero-warning actual PASS.')
    require(all(d[k]for k in ['only_standard_axioms','source_object_recorded_before_audit','all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit']),'Incomplete prior capture.')
    require((d['named_axiom_probes'],d['callers'])==(u['probes'],u['callers']),'Wrong prior census.')
    require((d['shared_timeout_seconds'],d['memory_mebibytes'],d['LEAN_NUM_THREADS'],d['global_option_overrides'])==(120,4096,'1',[]),'Changed prior limits.')
    require(not d['dependency_build']and not d['downloads']and not d['compiler_version_query_performed'],'Changed prior execution scope.')
    require(d['compiler']==b['compiler'],'Different prior compiler.')
    for path,h in d['before'].items():require(sha(path)==h,'Changed prior input '+path)
    for role in ['source','audit']:
        q=d[role];require(q['sha256']==u[role]['sha256']==sha(q['path'])==sha(q['snapshot']),'Prior source/audit differs.')
    require([c['label']for c in d['commands']]==['source','audit'],'Wrong prior command order.')
    for c in d['commands']:
        require(c['exit_code']==0 and not c['timed_out']and c['interrupted'] is None,'Prior command failed.')
        argv=c['command'];require(argv[:3]==[b['compiler']['path'],'-j1','-M4096']and len(argv)==(7 if c['label']=='source'else 5)and argv[3].startswith('--root=')and argv[-1]==d[c['label']]['snapshot'],'Unexpected prior argv.')
        require(sha(c['log'])==c['log_sha256']and Path(c['log']).read_text()==c['output'],'Changed prior raw log.')
        require('error:'not in c['output']and'warning:'not in c['output']and'sorryAx'not in c['output'],'Prior diagnostics.')
    rr=reports(d['commands'][1]['output']);require(rr==d['axiom_reports']and[q['name']for q in rr]==u['qualified_probes']and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong prior axiom reports.')
    f,=d['fresh_modules'];require(f['module']==module and f['source_sha256']==u['source']['sha256']and sha(f['path'])==f['sha256'],'Wrong prior fresh object.')
    require(all(d['source_pass_object'][k]==f[k]for k in ['module','path','sha256','source_sha256']),'Prior pre-audit capture differs.')
    cap=d['fresh_first_provider_before_audit'];require(cap['module']==module and Path(cap['path']).resolve()==Path(f['path']).resolve()and cap['sha256']==f['sha256'],'Wrong prior fresh first provider.')
    first={q['module']:q for q in d['actual_first_providers']};require(len(first)==len(d['actual_first_providers']),'Duplicate prior providers.')
    require(set(first)==set(q['module']for q in d['reused_modules']+d['toolchain_providers']),'Wrong prior provider census.')
    for q in d['reused_modules']:
        for k in ['source','object']:require(sha(q[k])==q[k+'_sha256']==d['before'][str(Path(q[k]).resolve())],'Wrong prior input binding.')
        require(Path(first[q['module']]['actual_first']).resolve()==Path(q['object']).resolve()and first[q['module']]['sha256']==q['object_sha256'],'Wrong prior actual provider.')
    for q in d['toolchain_providers']:
        require(sha(q['object'])==q['object_sha256']==d['before'][str(Path(q['object']).resolve())],'Wrong prior tool hash.')
        require(Path(first[q['module']]['actual_first']).resolve()==Path(q['object']).resolve()and first[q['module']]['sha256']==q['object_sha256'],'Wrong prior tool provider.')
    if not u.get('reused_pilot',False):
        pr=d['preparation'];require(sha(pr['path'])==pr['sha256'],'Changed prior preparation.')
        pp=json.loads(Path(pr['path']).read_text());require(pp['status']=='PREPARED_NOT_BUILT'and pp['prepare_only'] is True and pp['commands']==[]and pp['fresh_modules']==[]and pp['before']==pp['after']==d['before']and pp['all_input_provider_postchecks'],'Invalid prior preparation.')
    return d

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest',type=Path,default=HERE/'production-manifest.json')
    p.add_argument('--start',type=int,default=0);p.add_argument('--count',type=int,default=1)
    p.add_argument('--prior-batch',nargs=2,action='append',default=[],metavar=('PATH','SHA256'))
    p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
    require(__debug__ and MANIFEST_SHA is not None and sha(a.manifest)==MANIFEST_SHA,'Unfrozen/changed production manifest.')
    b=json.loads(a.manifest.read_text());order=b['order'];require(len(order)==len(set(order))==561,'Wrong generated unit order.')
    require((b['complete_units'],b['complete_probes'],b['complete_callers'])==(565,1062,1066),'Wrong complete census.')
    require(a.start>=0 and a.count>0 and a.start+a.count<=len(order),'Invalid selected range.')
    W=a.output.resolve();require(not W.exists()and not W.is_relative_to(Path('/home/codex/.codex/worktrees/ec20/Proofs'))and not W.is_relative_to(Path('/home/codex/src/Proofs')),'Fresh external batch directory required.')
    available={};prior=[]
    for module,ref in b['pilot_records'].items():successful(b,module,ref);available[module]=ref
    require(len(available)==4,'Require all four actual pilots.')
    for path,h in a.prior_batch:
        path=Path(path).resolve();require(re.fullmatch('[0-9a-f]{64}',h)and sha(path)==h,'Changed prior batch.');d=json.loads(path.read_text());prior.append(dict(path=str(path),sha256=h))
        require(d['manifest']['sha256']==MANIFEST_SHA and not d['prepare_only'],'Wrong or prepared prior batch.')
        for row in d['completed_units']:
            i=row['unit_index'];module=row['module'];require(0<=i<len(order)and order[i]==module and row['status']=='PASS','Wrong prior selected unit.')
            ref=row['record'];successful(b,module,ref)
            if module in available:require(available[module]==ref,'Conflicting prior actual records.')
            else:available[module]=ref
    selected=list(range(a.start,a.start+a.count));require(all(order[i]not in available for i in selected),'Already successful units must be reused.')
    W.mkdir(parents=True);r=dict(status='RUNNING',prepare_only=a.prepare_only,guard=descriptor(__file__),manifest=descriptor(a.manifest),selected_unit_indices=selected,prior_batches=prior,pilot_reuse=b['pilot_records'],completed_units=[],active_unit=None,failed_unit=None,serial=True,shared_timeout_seconds_per_unit=120,compiler_version_query_performed=False,dependency_build=False,downloads=False)
    def save():
        tmp=W/'batch.json.tmp';tmp.write_text(json.dumps(r,indent=2)+'\n');tmp.replace(W/'batch.json')
    save();i=None
    try:
        for i in selected:
            for ref in prior:require(sha(ref['path'])==ref['sha256'],'Prior batch changed.')
            module=order[i];u=b['units'][module];r['active_unit']=dict(index=i,module=module);save()
            require(all(m in available for m in u['future_parents']),'A required generated ancestor has not passed.')
            parents=[(m,available[m]['path'],available[m]['sha256'])for m in u['future_parents']]
            out=W/f'unit{i:03d}';run_unit(argparse.Namespace(unit=module,manifest=a.manifest,parent=parents,output=out,prepare_only=a.prepare_only))
            ref=descriptor(out/'verification.json');d=json.loads(Path(ref['path']).read_text())
            require(d['status']==('PREPARED_NOT_BUILT'if a.prepare_only else'PASS'),'Incomplete unit.')
            if not a.prepare_only:successful(b,module,ref);available[module]=ref
            r['completed_units'].append(dict(unit_index=i,module=module,status=d['status'],record=ref,preparation=descriptor(out/'preparation.json')));save()
        r.update(status='PREPARED_NOT_BUILT'if a.prepare_only else'PASS_SELECTED_UNITS',active_unit=None)
        if not a.prepare_only and all(m in available for m in order):
            for module in [*b['pilot_records'],*order]:successful(b,module,available[module])
            r.update(status='PASS_COMPLETE_COVERAGE',complete_generated_units=561,reused_pilot_units=4,complete_probes=1062,complete_callers=1066,final_record=available['BusyBeaver.ZFC.SitesRotation240'],selected_record_sha256_by_module={m:available[m]['sha256']for m in [*b['pilot_records'],*order]})
    except BaseException as ex:
        record=W/f'unit{i:03d}'/'verification.json' if i is not None else None
        r.update(status='FAIL',failed_unit=i,error=repr(ex),failed_record=descriptor(record)if record and record.is_file()else None,failure_stage='RECORDED_UNIT_FAILURE'if record and record.is_file()else'PREPARATION_REJECTED_BEFORE_COMPILER');save();raise
    save();print(W/'batch.json')
if __name__=='__main__':main()
