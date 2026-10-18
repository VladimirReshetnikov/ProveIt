#!/usr/bin/env python3
"""Exact first1024 Rotation244 blank prefix; four projects, no builds or version query."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path(__file__).resolve().parent
MODULE='BusyBeaver.ZFC.BootRotation244First'
PREFIX='SetTheory.BusyBeaver.ZFC.BootRotation244First.'
PROBES=['checkpoint0_rep','advance_checkpoint','block1024','first1024']
SOURCE_SHA='49b4228cde7fceeb25d820d5907422e352a19e883c4a1feb3d0548ead23cb76f'
AUDIT_SHA='b5f923b35e31bcc4a5d64a590baeb89d2b4b76010942ff3542717ef622b475db'
BOUNDARY_SHA='564ded89d98ccca8ff3f7c0a06b3aeba492f06bd9493c4c3fea6ed5b9b91ede6'
PARENT_SHA='d6b705cf3b0ab31e94edd01b0256c1a0a0553ae2d8640873e7c6803c58ec8feb'
GENERIC_SHA='c756bf41b8f2f778d0c6c21e8de0e54a3625cc69253607cb7e0f6fe1c3c605fb'
STANDARD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rel=lambda m,s='.olean':Path(m.replace('.','/')).with_suffix(s)
imports=lambda p:re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def require(x,msg):
    if not x:raise RuntimeError(msg)
def reports(text):
    rr=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in rr]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'BootRotation244First.lean')
    p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'boundary.json')
    p.add_argument('--parent-evidence',type=Path)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepare-only',action='store_true')
    a=p.parse_args();require(__debug__,'No optimized Python.')
    S,A,B,W=a.source.resolve(),a.audit.resolve(),a.boundary.resolve(),a.output.resolve()
    require(not W.exists()or(W.is_dir()and not any(W.iterdir())),'Fresh output required.')
    require(not W.is_relative_to(Path('/home/codex/.codex/worktrees/ec20/Proofs')) and not W.is_relative_to(Path('/home/codex/src/Proofs')),'External output only.')
    tracked={}
    def pin(p,h):
        p=Path(p).resolve();require(p.is_file()and sha(p)==h,'Changed input '+str(p))
        require(str(p)not in tracked or tracked[str(p)]==h,'Conflicting identity.')
        tracked[str(p)]=h;return p
    for p,h in [(S,SOURCE_SHA),(A,AUDIT_SHA),(B,BOUNDARY_SHA),(Path(__file__),sha(__file__))]:pin(p,h)
    b=json.loads(B.read_text())
    for q in b['static_inputs']:pin(q['path'],q['sha256'])
    inventory=json.loads(Path(b['static_inputs'][0]['path']).read_text())
    require(inventory['module']==MODULE and inventory['source']['sha256']==SOURCE_SHA and inventory['audit']['sha256']==AUDIT_SHA,'Wrong generated source/audit.')
    require(inventory['unit_index']==0 and inventory['start']==0 and inventory['endpoint']==1024 and inventory['final_target']==407931,'Wrong prefix interval.')
    require(inventory['segments']==[dict(start=0,end=1024,depth=10)] and inventory['probes']==[PREFIX+n for n in PROBES] and inventory['callers']==7,'Wrong generated contracts.')
    require([inventory[k]for k in ['data','generator','canonical']]==b['static_inputs'][1:],'Generated metadata descriptors differ.')
    data=json.loads(Path(inventory['data']['path']).read_text())
    require(data['status']=='UNTRUSTED_GENERATED_INPUTS' and data['proof_execution'] is False and data['segments']==inventory['segments'],'Generated inputs misclassified.')
    require(data['table']==inventory['canonical'] and inventory['proof_execution'] is False and inventory['guard_emitted'] is False,'Generated identity differs.')
    require(inventory['parents']==[dict(**b['parent'],module='BusyBeaver.ZFC.FastTableRotation244')],'Wrong generated Fast parent.')
    LE=pin(b['generic_provider_evidence']['path'],GENERIC_SHA);le=json.loads(LE.read_text())
    require(b['generic_provider_evidence']['sha256']==GENERIC_SHA and le['status']=='PASS' and not le['prepare_only'] and (le['named_axiom_probes'],le['callers'])==(3,4),'Wrong generic provider evidence.')
    require(le['before']==le['after'] and le['all_input_provider_postchecks'] and le['all_fresh_objects_unchanged_after_audit'] and le['only_standard_axioms'],'Incomplete generic evidence.')
    require([q['label']for q in le['commands']]==['source','audit'] and all(q['exit_code']==0 and not q.get('timed_out',False)for q in le['commands']),'Generic evidence commands failed.')
    E=pin(a.parent_evidence or b['parent']['path'],PARENT_SHA);e=json.loads(E.read_text())
    require(b['parent']['sha256']==PARENT_SHA and e['status']=='PASS'and(e['named_axiom_probes'],e['callers'])==(2,4),'Wrong parent.')
    require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete parent.')
    require([q['label']for q in e['commands']]==['source','audit']and all(q['exit_code']==0 and not q.get('timed_out',False)for q in e['commands']),'Parent command failure.')
    for path,digest in e['before'].items():pin(path,digest)
    for k in ['source','audit']:pin(e[k]['snapshot'],e[k]['sha256'])
    ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
    require(len(ns)==2 and [q['name']for q in rr]==ns and all(set(q['axioms'])<=STANDARD for q in rr),'Parent raw reports.')
    require(imports(S)==['BusyBeaver.ZFC.FastTableRotation244','BusyBeaver.ZFC.FiniteZipper']and imports(A)==[MODULE],'Imports changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES],'Audit qualified names changed.')
    require(len(re.findall(r'^example\b',A.read_text(),re.M))==7,'Typed callers changed.')
    for p in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',p.read_text()),'Untrusted proof exit.')
        require(not re.search(r'\bset_option\b',p.read_text()),'Raised proof limits.')
    reused=b['reused_modules'];tools=b['toolchain_providers'];projects={q['module']:q for q in reused}
    require(len(reused)==4 and set(projects)=={'BusyBeaver.Core','BusyBeaver.ZFC.TableRotation244','BusyBeaver.ZFC.FastTableRotation244','BusyBeaver.ZFC.FiniteZipper'},'Wrong selected projects.')
    C=pin(b['compiler']['path'],b['compiler']['sha256']);require(b['compiler']==e['compiler'] and Path(le['compiler']['path']).resolve()==C and le['compiler']['sha256']==sha(C),'Different compiler.')
    require(e['source_object_recorded_before_audit'] and len(e['fresh_modules'])==1,'Missing selected parent source capture.')
    fresh=e['fresh_modules'][0]
    require(fresh['module']=='BusyBeaver.ZFC.FastTableRotation244' and e['source_pass_object']==dict(fresh,source_command_index=0),'Wrong parent fresh object.')
    parent_first=e['fresh_first_provider_before_audit']
    require(parent_first['module']==fresh['module'] and parent_first['sha256']==fresh['sha256'] and
            Path(parent_first['path']).resolve()==Path(fresh['path']).resolve(),'Parent fresh first provider differs.')
    require(sha(fresh['path'])==fresh['sha256'] and fresh['source_sha256']==e['source']['sha256'],'Parent source/object binding differs.')
    for q in reused:
        if q['module'] in {'BusyBeaver.Core','BusyBeaver.ZFC.TableRotation244'}:
            old=next(x for x in e['reused_modules']if x['module']==q['module']);require(q==old,'Changed Fast-parent provider pair.')
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==e['after'].get(str(pp))==q[k+'_sha256'],'Absent parent pair input.')
            old=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            require(Path(old['actual_first']).resolve()==Path(q['object']).resolve()and old['sha256']==q['object_sha256'],'Wrong historical Fast-parent provider.')
        elif q['module']=='BusyBeaver.ZFC.FiniteZipper':
            old=next(x for x in le['reused_modules']if x['module']==q['module']);require(q==old,'Changed generic pair.')
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(le['before'].get(str(pp))==le['after'].get(str(pp))==q[k+'_sha256'],'Absent generic pair input.')
            old=next(x for x in le['actual_first_providers']if x['module']==q['module'])
            require(Path(old['actual_first']).resolve()==Path(q['object']).resolve() and old['sha256']==q['object_sha256'],'Wrong historical generic provider.')
        else:
            require(q['source_sha256']==e['source']['sha256'] and q['object_sha256']==fresh['sha256'] and
                    Path(q['object']).resolve()==Path(fresh['path']).resolve(),'Wrong selected Fast pair.')
            pin(q['source'],q['source_sha256']);pin(q['object'],q['object_sha256'])
    require(tools==le['toolchain_providers'] and {q['module']for q in tools}=={'Init','Lean.Elab.Tactic.Omega'},'Wrong tool boundary.')
    for q in tools:
        pp=pin(q['object'],q['object_sha256']);require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool reference mismatch.')
        require(le['before'].get(str(pp))==le['after'].get(str(pp))==q['object_sha256'],'Absent generic tool input.')
        if q['module']=='Init':
            iq=next(x for x in e['toolchain_providers']if x['module']=='Init');require(iq['object_sha256']==q['object_sha256'] and Path(iq['object']).resolve()==pp,'Parent tool conflict.')
    seen=set();toolnames={'Init'}
    def visit(m):
        if m in {'Init','Lean.Elab.Tactic.Omega'}:toolnames.add(m);return
        require(m in projects,'Unselected import '+m)
        if m in seen:return
        seen.add(m)
        for n in imports(projects[m]['source']):visit(n)
    for m in imports(S):visit(m)
    require(seen==set(projects)and toolnames=={q['module']for q in tools},'Wrong DFS.')
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
    actual=providers();env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',LEAN_SYSROOT=str(C.parent.parent))
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope='Exact first1024 Rotation244 blank prefix with complete tape readback. Remaining407931 chain/runtime/consistency and PA are separate.',source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=[dict(path=str(E),sha256=PARENT_SHA),dict(path=str(LE),sha256=GENERIC_SHA)],compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,toolchain_providers=tools,actual_first_providers=actual,exact_project_import_closure=sorted(seen),exact_project_prerequisite_count=4,before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['scope'])
    def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
    def post():
        r['after']={p:sha(p)for p in tracked};require(r['before']==r['after']and providers()==actual,'Postcheck failed.')
        for q in r['fresh_modules']:require(first(q['module'])==Path(q['path']).resolve()and sha(q['path'])==q['sha256'],'Fresh object changed.')
        r['all_input_provider_postchecks']=True
    save()
    try:
        if a.prepare_only:post();save();print(W/'verification.json');return
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
        out=run('audit',aa);rr=reports(out);require([q['name']for q in rr]==[PREFIX+n for n in PROBES]and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong actual reports.')
        post();r.update(status='PASS',named_axiom_probes=4,callers=7,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
