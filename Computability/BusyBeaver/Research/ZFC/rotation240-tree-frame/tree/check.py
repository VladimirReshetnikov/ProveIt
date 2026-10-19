#!/usr/bin/env python3
"""Complete literal rotated source tree; ten exact project providers and Init."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-tree-rotation240')
MODULE='BusyBeaver.ZFC.TreeRotation240'
PREFIX='SetTheory.BusyBeaver.ZFC.TreeRotation240.'
PROBES=['tree_eq_fuel', 'tree_eq', 'walk_eq_tree', 'step_eq_tree', 'leaf_count', 'node_count', 'depth_eq', 'halt_count']
SOURCE_SHA='725e32894e0d9caf5b07d8f93c5f914f86ce92088cdf1ac399bad6dc10993224'
AUDIT_SHA='00e93a3808997abf364d835fc724ffa6f71cdb56856575470a18acc4bac7617d'
BOUNDARY_SHA='ad7f5e159820d2947f78b7f3caff8bd62e270f6c2ad9d704a85d610ab00840ae'
PARENT_SHA='aa9d314ede4bb61c5f1962a2390bd6e3d064ab4778597914458e977aded24c7c'
PARENT_SOURCE_SHA='bbda8dae8ce42e890b8ad6bd8b22bf62275f0ae0114f8d2350ac558a2e5ac21b'
PARENT_AUDIT_SHA='1d917d7c124b0349b933051369726959ff0aa8f69f2a51fcdca13825ff3905f7'
PARENT_AUDIT_NAMES=['SetTheory.BusyBeaver.ZFC.SourceRotation240.program_root', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.program_nnodes', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.node169', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.nodes_unmodified', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.new_program_eq', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.new_wf', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.local_run_iff', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.replacement', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.iterHalts_iff', 'SetTheory.BusyBeaver.ZFC.SourceRotation240.program_halts_iff']
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
    p.add_argument('--source',type=Path,default=HERE/'generated-v1/TreeRotation240.lean')
    p.add_argument('--audit',type=Path,default=HERE/'generated-v1/Audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'boundary.json')
    p.add_argument('--parent-evidence',type=Path)
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
    E=pin(a.parent_evidence or b['parent']['path'],PARENT_SHA);e=json.loads(E.read_text())
    require(b['parent']['sha256']==PARENT_SHA and e['status']=='PASS'and(e['named_axiom_probes'],e['callers'])==(10,13),'Wrong parent.')
    require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete parent.')
    require([q['label']for q in e['commands']]==['source','audit']and all(q['exit_code']==0 and not q.get('timed_out',False)for q in e['commands']),'Parent command failure.')
    require(not e['prepare_only'] and e['warnings']==0 and (e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[]),'Parent limits/status changed.')
    require(not any(e[k] for k in ['compiler_version_query_performed','dependency_build','downloads']),'Parent execution scope changed.')
    require(e['source']['sha256']==PARENT_SOURCE_SHA and e['audit']['sha256']==PARENT_AUDIT_SHA,'Parent source/audit identity mismatch.')
    for pp,hh in e['before'].items():pin(pp,hh)
    for c in e['commands']:
        log=pin(c['log'],c['log_sha256']);require(log.read_text()==c['output'] and c['command'][:3]==[e['compiler']['path'],'-j1','-M4096'] and not c.get('interrupted'),'Parent raw log/command mismatch.')
    for k in ['source','audit']:pin(e[k]['snapshot'],e[k]['sha256'])
    ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
    require(ns==PARENT_AUDIT_NAMES and [q['name']for q in rr]==ns and all(set(q['axioms'])<=STANDARD for q in rr),'Parent raw reports.')
    require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==13,'Parent caller census.')
    for c in e['commands']:
        pin(c['log'],hashlib.sha256(c['output'].encode()).hexdigest())
    require(imports(S)==['BusyBeaver.ZFC.SourceRotation240']and imports(A)==[MODULE],'Imports changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES],'Audit qualified names changed.')
    require(len(re.findall(r'^example\b',A.read_text(),re.M))==10,'Typed callers changed.')
    for p in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',p.read_text()),'Untrusted proof exit.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text()),'Raised proof limits.')
    reused=b['reused_modules'];tools=b['toolchain_providers'];projects={q['module']:q for q in reused}
    require(len(reused)==10 and set(projects)==set(['BusyBeaver.ZFC.ProgramRotation244', 'BusyBeaver.ZFC.ProgramRouting245', 'BusyBeaver.ZFC.RMBisim', 'BusyBeaver.ZFC.RMDag', 'BusyBeaver.ZFC.RMDagContextSubstitution', 'BusyBeaver.ZFC.RMDagLoopRotation', 'BusyBeaver.ZFC.RMEquiv', 'BusyBeaver.ZFC.RegisterPath', 'BusyBeaver.ZFC.SourceRotation240', 'BusyBeaver.ZFC.SourceRotation244']),'Wrong selected projects.')
    C=pin(b['compiler']['path'],b['compiler']['sha256']);require(b['compiler']==e['compiler'],'Different compiler.')
    for q in reused:
        if q['module'] == 'BusyBeaver.ZFC.SourceRotation240':
            fs=e['fresh_modules'];require(len(fs)==1 and fs[0]['module']==q['module'],'Wrong fresh parent module.')
            f=fs[0];require(q['source']==e['source']['path']and q['source_sha256']==e['source']['sha256']==f['source_sha256']and q['object']==f['path']and q['object_sha256']==f['sha256'],'Fresh parent identity mismatch.')
            for k in ['source','object']:pin(q[k],q[k+'_sha256'])
            require(e['source_object_recorded_before_audit']and e['source_pass_object']==dict(f,source_command_index=0),'Missing fresh pre-audit capture.')
            cap=e['fresh_first_provider_before_audit'];require(cap['module']==q['module']and Path(cap['path']).resolve()==Path(q['object']).resolve()and cap['sha256']==q['object_sha256'],'Wrong fresh first provider.')
        else:
            old=next(x for x in e['reused_modules']if x['module']==q['module']);require(q==old,'Changed selected parent pair.')
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==e['after'].get(str(pp))==q[k+'_sha256'],'Absent parent pair input.')
            old=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            require(Path(old['actual_first']).resolve()==Path(q['object']).resolve()and old['sha256']==q['object_sha256'],'Wrong historical first provider.')
    require(tools==e['toolchain_providers']and {q['module']for q in tools}=={'Init'},'Wrong tool boundary.')
    for q in tools:
        pp=pin(q['object'],q['object_sha256']);require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool reference mismatch.')
        require(e['before'].get(str(pp))==e['after'].get(str(pp))==q['object_sha256'],'Absent parent tool input.')
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
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope='Exact SourceRotation240.program tree for every sufficient fuel, arbitrary pointers/registers;6455leaves/6454nodes/depth51/onehalt. Binary runtime, coverage, bootstrap and calibration remain separate.',source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=[dict(path=str(E),sha256=PARENT_SHA)],compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,toolchain_providers=tools,actual_first_providers=actual,exact_project_import_closure=sorted(seen),exact_project_prerequisite_count=10,before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['scope'])
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
        post();r.update(status='PASS',named_axiom_probes=8,callers=10,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
