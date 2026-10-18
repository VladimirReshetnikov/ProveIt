#!/usr/bin/env python3
"""Exact Rotation244 continuation; one actual predecessor and selected current closure."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
CFG = {'module': 'BusyBeaver.ZFC.BootRotation244Chunk005', 'source_sha256': '802a3276774076543a4efe24e0a62654cf370a57e25df4bd286f4b67929325f9', 'audit_sha256': '2f604750610e7252d1814f42c810f1ef1cbc067f66ffe6521b91e6c738eeb942', 'boundary_sha256': '21135638c21ce910b3dcc67a91fa227cffab030992e1d714f59736c85bf1003d', 'parent_sha256': 'e7ae197b2bcd737c854e955de53c09c4e77c99f4ef6b61e689043efedcaa6f8c', 'parent_module': 'BusyBeaver.ZFC.BootRotation244Chunk004', 'parent_census': [8, 11], 'index': 5, 'start': 214016, 'end': 279552, 'segments': [{'start': 214016, 'end': 230400, 'depth': 14}, {'start': 230400, 'end': 246784, 'depth': 14}, {'start': 246784, 'end': 263168, 'depth': 14}, {'start': 263168, 'end': 279552, 'depth': 14}], 'probes': ['block230400', 'reached230400', 'block246784', 'reached246784', 'block263168', 'reached263168', 'block279552', 'reached279552'], 'callers': 11, 'project_count': 9}
HERE=Path(__file__).resolve().parent
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
    require(isinstance(CFG,dict),'Unbound template; freeze actual source and predecessor first.')
    MODULE=CFG['module'];PREFIX='SetTheory.BusyBeaver.ZFC.'+MODULE.rsplit('.',1)[1]+'.'
    SOURCE_SHA=CFG['source_sha256'];AUDIT_SHA=CFG['audit_sha256'];BOUNDARY_SHA=CFG['boundary_sha256'];PARENT_SHA=CFG['parent_sha256'];PROBES=CFG['probes'];CALLERS=CFG['callers']
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/(MODULE.rsplit('.',1)[1]+'.lean'))
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
    for pp,h in [(S,SOURCE_SHA),(A,AUDIT_SHA),(B,BOUNDARY_SHA),(Path(__file__),sha(__file__))]:pin(pp,h)
    b=json.loads(B.read_text())
    for q in b['static_inputs']:pin(q['path'],q['sha256'])
    inventory=json.loads(Path(b['inventory']['path']).read_text());data=json.loads(Path(inventory['data']['path']).read_text())
    require(inventory['module']==MODULE and inventory['source']['sha256']==SOURCE_SHA and inventory['audit']['sha256']==AUDIT_SHA,'Wrong generated source/audit.')
    require(inventory['unit_index']==CFG['index'] and inventory['start']==CFG['start'] and inventory['endpoint']==CFG['end'] and inventory['final_target']==407931,'Wrong prefix interval.')
    require(inventory['segments']==CFG['segments'] and inventory['probes']==[PREFIX+n for n in PROBES] and inventory['callers']==CALLERS,'Wrong generated contracts.')
    require([inventory[k]for k in ['data','generator','canonical']]==b['generated_payloads'],'Wrong generated payloads.')
    require(data['status']=='UNTRUSTED_GENERATED_INPUTS' and data['proof_execution'] is False and data['segments']==inventory['segments'] and data['table']==inventory['canonical'],'Wrong untrusted data binding.')
    require(inventory['proof_execution'] is False and inventory['guard_emitted'] is False,'Generated status changed.')
    previous=json.loads(Path(b['previous_inventory']['path']).read_text())
    require(previous['module']==CFG['parent_module'] and previous['unit_index']==CFG['index']-1 and previous['endpoint']==CFG['start'],'Wrong preceding inventory API.')
    require(inventory['parents']==[dict(**b['parent'],module=CFG['parent_module'])] and inventory['metadata_inputs']==[b['previous_inventory']],'Wrong selected predecessor.')
    E=pin(a.parent_evidence or b['parent']['path'],PARENT_SHA);e=json.loads(E.read_text())
    require(b['parent']['sha256']==PARENT_SHA and e['status']=='PASS' and e['prepare_only'] is False and (e['named_axiom_probes'],e['callers'])==tuple(CFG['parent_census']),'Wrong parent.')
    require(e['before']==e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'],'Incomplete parent.')
    require([q['label']for q in e['commands']]==['source','audit'] and all(q['exit_code']==0 and not q.get('timed_out',False) and q.get('interrupted') is None for q in e['commands']),'Parent command failure.')
    for k in ['source','audit']:
        pp=pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
        require(e['before'].get(str(pp))==e['after'].get(str(pp))==e[k]['sha256'],'Absent parent source/audit input.')
        require(previous[k]['sha256']==e[k]['sha256'],'Previous inventory source/audit differs.')
    ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
    require(len(ns)==CFG['parent_census'][0] and [q['name']for q in rr]==ns and all(set(q['axioms'])<=STANDARD for q in rr),'Parent raw reports.')
    require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==CFG['parent_census'][1],'Parent caller census.')
    require(imports(S)==[CFG['parent_module']] and imports(A)==[MODULE],'Imports changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES],'Audit qualified names changed.')
    require(len(re.findall(r'^example\b',A.read_text(),re.M))==CALLERS,'Typed callers changed.')
    for pp in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',pp.read_text()),'Untrusted proof exit.')
        require(not re.search(r'\bset_option\b',pp.read_text()),'Raised proof limits.')
    reused=b['reused_modules'];tools=b['toolchain_providers'];projects={q['module']:q for q in reused}
    require(len(projects)==len(reused)==CFG['project_count'] and CFG['project_count']==4+CFG['index'],'Wrong selected project census.')
    C=pin(b['compiler']['path'],b['compiler']['sha256']);require(b['compiler']==e['compiler'],'Different compiler.')
    require(all(q['command'][:3]==[str(C),'-j1','-M4096']for q in e['commands']),'Parent execution flags differ.')
    require(e['source_object_recorded_before_audit'] and len(e['fresh_modules'])==1,'Missing selected parent source capture.')
    fresh=e['fresh_modules'][0]
    require(fresh['module']==CFG['parent_module'] and e['source_pass_object']==dict(fresh,source_command_index=0),'Wrong parent fresh object.')
    parent_first=e['fresh_first_provider_before_audit']
    require(parent_first['module']==fresh['module'] and parent_first['sha256']==fresh['sha256'] and Path(parent_first['path']).resolve()==Path(fresh['path']).resolve(),'Parent fresh first provider differs.')
    require(sha(fresh['path'])==fresh['sha256'] and fresh['source_sha256']==e['source']['sha256'],'Parent source/object binding differs.')
    old_providers={q['module']:q for q in e['reused_modules']}
    require(set(projects)==set(old_providers)|{CFG['parent_module']} and CFG['parent_module']not in old_providers,'Wrong predecessor closure union.')
    for q in reused:
        if q['module'] in old_providers:
            require(q==old_providers[q['module']],'Changed predecessor provider pair.')
            for k in ['source','object']:
                pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==e['after'].get(str(pp))==q[k+'_sha256'],'Absent parent pair input.')
            old=next(x for x in e['actual_first_providers']if x['module']==q['module'])
            require(Path(old['actual_first']).resolve()==Path(q['object']).resolve() and old['sha256']==q['object_sha256'],'Wrong historical provider.')
        else:
            require(q['source_sha256']==e['source']['sha256'] and Path(q['source']).resolve()==Path(e['source']['path']).resolve() and q['object_sha256']==fresh['sha256'] and Path(q['object']).resolve()==Path(fresh['path']).resolve(),'Wrong fresh provider pair.')
            pin(q['source'],q['source_sha256']);pin(q['object'],q['object_sha256'])
    require(tools==e['toolchain_providers'] and {q['module']for q in tools}=={'Init','Lean.Elab.Tactic.Omega'},'Wrong tool boundary.')
    for q in tools:
        pp=pin(q['object'],q['object_sha256']);require(pp==C.parent.parent/'lib/lean'/rel(q['module']),'Tool reference mismatch.')
        require(e['before'].get(str(pp))==e['after'].get(str(pp))==q['object_sha256'],'Absent parent tool input.')
        old=next(x for x in e['actual_first_providers']if x['module']==q['module'])
        require(Path(old['actual_first']).resolve()==pp and old['sha256']==q['object_sha256'],'Wrong historical tool provider.')
    seen=set();toolnames={'Init'}
    def visit(m):
        if m in {'Init','Lean.Elab.Tactic.Omega'}:toolnames.add(m);return
        require(m in projects,'Unselected import '+m)
        if m in seen:return
        seen.add(m)
        for n in imports(projects[m]['source']):visit(n)
    for m in imports(S):visit(m)
    require(seen==set(projects) and toolnames=={q['module']for q in tools},'Wrong DFS.')
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
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope=b['scope'],source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=[dict(path=str(E),sha256=PARENT_SHA)],compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,toolchain_providers=tools,actual_first_providers=actual,exact_project_import_closure=sorted(seen),exact_project_prerequisite_count=CFG['project_count'],before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=str(cache),LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['scope'])
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
        post();r.update(status='PASS',named_axiom_probes=len(PROBES),callers=CALLERS,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
