#!/usr/bin/env python3
"""Concrete Combined243 versus Rotation244 whole-run simulation; exact three parents/seven projects."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path(__file__).resolve().parent
REPO=HERE.parents[3]
MODULE='BusyBeaver.ZFC.Combined243Simulation'
PREFIX='SetTheory.BusyBeaver.ZFC.Combined243Simulation.'
PROBES=['simulation','start_halts_iff','blank_halts_iff','blank_nonhalts_iff']
SOURCE_SHA='85fcfb12740f6ce57425945b9d92429d58d426b7d893d3c7734f3acc515c9a31'
AUDIT_SHA='ca02e99bcc39b913f1cf324e6250aa92baea16f5bd1d908fb01deb907abc27a6'
BOUNDARY_SHA='8fdf6167b0ef2fc9b285e347f8110a646773988cbecc351295e15c3fab2e3805'
PARENT_SHAS={'positive': '39d7b8257fc41468782322c1131e81c8ffdef34edccd61ec539419a205bdd420', 'invariant': '76cf8e6e038f187b336908c860227375eb5bfdfbdd6a52e644ef7c18ec03c6d0', 'blocks': 'e4ebb3fcf294760563409069fae6211593bd7fcbd07b428438819db1fc684cb7'}
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
    p.add_argument('--source',type=Path,default=REPO/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Combined243Simulation.lean')
    p.add_argument('--audit',type=Path,default=HERE/'combined243_simulation_audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'combined243-formal/simulation/boundary.json')
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
    C=pin(b['compiler']['path'],b['compiler']['sha256']);pool={};alltools={};parent_records=[]
    for key,desc in b['parents'].items():
        E=pin(desc['path'],PARENT_SHAS[key]);require(desc['sha256']==PARENT_SHAS[key],'Parent boundary mismatch.');e=json.loads(E.read_text())
        require(e['status']=='PASS'and(e['named_axiom_probes'],e['callers'])==(desc['probes'],desc['callers']),'Wrong parent outcome.')
        require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete parent.')
        require([q['label']for q in e['commands']]==['source','audit']and all(q['exit_code']==0 and not q.get('timed_out',False)for q in e['commands']),'Failed parent commands.')
        require(all(e['compiler'][k]==b['compiler'][k]for k in ['path','version','sha256']),'Compiler identity differs.')
        for pp,h in e['before'].items():pin(pp,h)
        for k in ['source','audit']:pin(e[k]['snapshot'],e[k]['sha256'])
        ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        require(ns==desc['audit_names']and len(ns)==desc['probes']and [q['name']for q in rr]==desc['report_names']and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong raw parent audit names/axioms.')
        require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==desc['callers'],'Wrong parent callers.')
        require(desc['report_names']==ns,'Unexpected parent namespace.')
        fs=e['fresh_modules'];require(len(fs)==1,'Wrong parent fresh count.');f=fs[0]
        require(e['source_object_recorded_before_audit']and all(e['source_pass_object'][k]==f[k]for k in ['module','path','sha256','source_sha256']),'Missing parent fresh capture.')
        require(e['source_pass_object']['source_command_index']==0 and f['source_sha256']==e['source']['sha256'],'Wrong source capture binding.')
        cap=e['fresh_first_provider_before_audit'];require(cap['module']==f['module']and Path(cap['path']).resolve()==Path(f['path']).resolve()and cap['sha256']==f['sha256'],'Fresh parent first mismatch.');pin(f['path'],f['sha256'])
        for q in e['reused_modules']:
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==e['after'].get(str(pp))==q[k+'_sha256'],'Absent parent import input.')
            actual=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            require(Path(actual['actual_first']).resolve()==Path(q['object']).resolve()and actual['sha256']==q['object_sha256'],'Wrong historical first import.')
        for q in e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]:
            row={k:q[k]for k in ['module','source','source_sha256','object','object_sha256']}
            require(q['module']not in pool or pool[q['module']]==row,'Conflicting shared project pair.');pool[q['module']]=row
        require(sorted(q['module']for q in e['toolchain_providers'])==desc['tools'],'Wrong parent tool selection.')
        for q in e['toolchain_providers']:
            row={k:q[k]for k in ['module','object','object_sha256']};pp=pin(q['object'],q['object_sha256'])
            require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool reference mismatch.')
            require(q['module']not in alltools or alltools[q['module']]==row,'Conflicting tool identity.');alltools[q['module']]=row
        parent_records.append(dict(path=str(E),sha256=PARENT_SHAS[key],module=f['module']))
    reused=b['reused_modules'];tools=b['toolchain_providers'];projects={q['module']:q for q in reused}
    require(projects==pool and len(pool)==7 and {q['module']:q for q in tools}==alltools and set(alltools)=={'Init','Lean.Elab.Tactic.Omega'},'Wrong seven-project/two-tool union.')
    require(imports(S)==['BusyBeaver.ZFC.PositiveBlockBisimulation','BusyBeaver.ZFC.Rotation244Invariant','BusyBeaver.ZFC.Combined243Blocks']and imports(A)==[MODULE],'Changed source imports.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==4,'Wrong audit4/4.')
    for pp in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',pp.read_text()),'Untrusted proof exit.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',pp.read_text()),'Raised proof limits.')
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
    actual=providers();env=dict(os.environ,LEAN_PATH=str(cache),LEAN_NUM_THREADS='1')
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope='Combined243 versus Rotation244 positive-block simulation, arbitrary finite-support start tapes and exact blank halting/nonhalting iff. No consistency calibration, PA internalization or infinite-support tape claim.',source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=parent_records,compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,toolchain_providers=tools,actual_first_providers=actual,exact_project_import_closure=sorted(seen),exact_project_prerequisite_count=7,before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['scope'])
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
        post();r.update(status='PASS',named_axiom_probes=4,callers=4,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
