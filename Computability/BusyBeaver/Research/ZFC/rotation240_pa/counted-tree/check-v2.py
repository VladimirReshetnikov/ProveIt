#!/usr/bin/env python3
"""CountedTreeRotation240; thirteen actual project prerequisites and Init, 3/3 audit.
Shared 120 seconds, -j1 -M4096, default new proof limits; no builds or queries."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-w6-counted-tree240/draft2')
MODULE='BusyBeaver.ZFC.CountedTreeRotation240'
PREFIX='SetTheory.BusyBeaver.ZFC.CountedTreeRotation240.'
PROBES=['counted_eq','leaf_count','catalogue_length']
SOURCE_SHA='8918d46a4f050622f8a2392f6ba7a0aeab97dabcd33dd2b2853ab3c5cefeb925'
AUDIT_SHA='d3638ca00e1d029550631b18ac62d92f7a79e2b97db465eb34034dadb7c894e6'
BOUNDARY_SHA='60e95ccc9d5fde3e08625b6b23b8beeabc8ccd228e1a587a1f79b6fe423136aa'
PARENT_PINS={'catalogue': '3d45099665953c442332ea947985ac7cc96cfec0063c8b148b855b9abde99f21', 'tree': '356fd76abe9099ecc69ecd26fbae5678005792343cfc454c203d90515be35a82'}
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
    p.add_argument('--source',type=Path,default=HERE/'CountedTreeRotation240.lean')
    p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    p.add_argument('--boundary',type=Path,default=Path(__file__).resolve().with_name('boundary-v2.json'))
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepare-only',action='store_true')
    a=p.parse_args();require(__debug__,'No optimized Python.')
    require(isinstance(SOURCE_SHA,str) and isinstance(BOUNDARY_SHA,str),'Pending generated source/boundary pins: root emission required.')
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
    require({q['label']:q['record']['sha256']for q in b['parents']}==PARENT_PINS,'Wrong exact parent pins.')
    pool={};evidence=[];C=pin(b['compiler']['path'],b['compiler']['sha256']);parent_tools=None
    for spec in b['parents']:
        E=pin(spec['record']['path'],PARENT_PINS[spec['label']]);e=json.loads(E.read_text());evidence.append(dict(path=str(E),sha256=PARENT_PINS[spec['label']]))
        require(e['status']=='PASS' and not e['prepare_only'] and (e['named_axiom_probes'],e['callers'])==(spec['probes'],spec['callers']),'Wrong completed parent.')
        require(e['before']==e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'],'Incomplete parent postchecks.')
        require(len(e['before'])==spec['before_inputs'] and len(e['reused_modules'])==spec['project_inputs'],'Wrong parent census.')
        require(e['warnings']==0 and (e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[]),'Changed parent policy.')
        require(e['compiler']==b['compiler'] and not any(e[k]for k in ['compiler_version_query_performed','dependency_build','downloads']),'Changed parent compiler/scope.')
        require(not e.get('providers',[]),'Unexpected external parent boundary.')
        for pp,hh in e['before'].items():pin(pp,hh)
        for role in ['source','audit']:
            require(e[role]['sha256']==spec[role+'_sha256'],'Parent source/audit identity.')
            pin(e[role]['path'],e[role]['sha256']);pin(e[role]['snapshot'],e[role]['sha256'])
        f,=e['fresh_modules'];pin(f['path'],f['sha256'])
        require(f['module']==spec['module'] and f['source_sha256']==spec['source_sha256'] and f['sha256']==spec['fresh_object_sha256'],'Wrong parent fresh object.')
        require(e['source_object_recorded_before_audit'] and e['source_pass_object']==dict(f,source_command_index=0),'Missing parent pre-audit capture.')
        require(e['fresh_first_provider_before_audit']=={k:f[k]for k in ('module','path','sha256')},'Wrong parent fresh first capture.')
        require([q['label']for q in e['commands']]==['source','audit'],'Parent command order.')
        for command in e['commands']:
            require(command['exit_code']==0 and not command['timed_out'] and not command.get('interrupted'),'Parent command failure.')
            expected=[str(C),'-j1','-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if command['label']=='source'else[])+[e[command['label']]['snapshot']]
            require(command['command']==expected,'Exact parent command mismatch.')
            log=pin(command['log'],command['log_sha256']);require(log.read_text()==command['output'],'Changed raw parent output.')
        audit_text=Path(e['audit']['snapshot']).read_text();ns=re.findall(r'^#print axioms (\S+)$',audit_text,re.M);rr=reports(e['commands'][1]['output'])
        require(len(ns)==spec['probes'] and ns==[q['name']for q in rr] and rr==e['axiom_reports'] and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong parent raw reports.')
        require(len(re.findall(r'^example\b',audit_text,re.M))==spec['callers'],'Wrong parent caller census.')
        first_rows={q['module']:q for q in e['actual_first_providers']}
        require(len(first_rows)==len(e['actual_first_providers']) and set(first_rows)=={q['module']for q in e['reused_modules']+e['toolchain_providers']},'Wrong historical first-provider census.')
        for q in e['reused_modules']+e['toolchain_providers']:
            for k in ['source','object']:
                if k in q:
                    pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==q[k+'_sha256'],'Unbound parent pair.')
            old=first_rows[q['module']];require(Path(old['actual_first']).resolve()==Path(q['object']).resolve() and old['sha256']==q['object_sha256'],'Wrong historical first provider.')
        fresh=dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'],evidence=str(E))
        for q in e['reused_modules']+[fresh]:
            if q['module']in pool:require(all(pool[q['module']][k]==q[k]for k in ['source','source_sha256','object','object_sha256']),'Conflicting source/object identity.')
            else:pool[q['module']]=q
        if parent_tools is None:parent_tools=e['toolchain_providers']
        else:require(parent_tools==e['toolchain_providers'],'Conflicting tool boundary.')
    require(imports(S)==['BusyBeaver.ZFC.ControlCatalogue','BusyBeaver.ZFC.TreeRotation240'] and imports(A)==[MODULE],'Imports changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES],'Audit qualified names changed.')
    require(len(re.findall(r'^example\b',A.read_text(),re.M))==3,'Typed callers changed.')
    for p in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',p.read_text()),'Untrusted proof exit.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text()),'Raised proof limits.')
    reused=b['reused_modules'];tools=b['toolchain_providers'];projects={q['module']:q for q in reused}
    require(len(reused)==len(projects)==13 and set(projects)==set(pool)==set(b['expected_projects']),'Wrong exact selected project union.')
    for q in reused:
        require(all(q[k]==pool[q['module']][k]for k in ['source','source_sha256','object','object_sha256']),'Changed selected source/object.')
        for k in ['source','object']:pin(q[k],q[k+'_sha256'])
    require(tools==parent_tools and len(tools)==1 and tools[0]['module']=='Init','Wrong Init boundary.')
    for q in tools:
        pp=pin(q['object'],q['object_sha256']);require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool root mismatch.')
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
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope='Exact cached counted annotation of TreeRotation240.tree and its 6455-leaf catalogue length. No packed table equality, row-check acceptance or binary simulation is asserted.',source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=evidence,compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,toolchain_providers=tools,actual_first_providers=actual,exact_project_import_closure=sorted(seen),exact_project_prerequisite_count=13,before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['scope'])
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
        post();r.update(status='PASS',named_axiom_probes=3,callers=3,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
