#!/usr/bin/env python3
"""Fresh Zermelo model APIs; actual Basic and ExistsUnique with scoped cached boundaries."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-foundation-z-route/next/z')
MODULE='Foundation.FirstOrder.SetTheory.Z'
PREFIX='LO.FirstOrder.SetTheory.'
PROBES=['mem_ext_iff', 'empty_exists', 'not_mem_empty', 'pairing_exists', 'union_exists', 'power_exists', 'separation_exists_eval', 'empty_mem_ω', 'ω_succ_closed', 'mem_succ_iff', 'naturalNumber_induction', 'foundation']
SOURCE_SHA='3eb45f3ee9629a888206aba4bc961b9ce35bab805e1b3b35535b4b2e0959e612'
AUDIT_SHA='c30c876d175229e63e819e2adb8702043194896f71888fc01f99e6052f898acd'
BOUNDARY_SHA='7dc5acb2c4439d54d79fa77bad49e2755861f07a7786cedef74fd5dc59b3151d'
PARENT_SHAS=['a410186f551fd7b8c8c41e40f8b38c38a639071ffe90d9bdb427b72ecd5ac49c', '98d0b89c6a5ab68e799bf921efa47fce48e29d0e93575f037bc342932f4e1710']
STANDARD={'propext','Classical.choice','Quot.sound'}
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rel=lambda m,s='.olean':Path(m.replace('.','/')).with_suffix(s)
imports=lambda p:re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def require(x,msg):
    if not x:raise RuntimeError(msg)
def reports(text):
    rr=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in rr]
def artifacts(p):
    p=Path(p);return [dict(path=str(q.resolve()),sha256=sha(q))for q in [p,Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')]if q.is_file()]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'Z.lean');p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
    p.add_argument('--boundary',type=Path,default=HERE/'boundary.json');p.add_argument('--output',type=Path,required=True)
    p.add_argument('--prepare-only',action='store_true');a=p.parse_args();require(__debug__,'No optimized Python.')
    S,A,B,W=a.source.resolve(),a.audit.resolve(),a.boundary.resolve(),a.output.resolve()
    require(not W.exists()or(W.is_dir()and not any(W.iterdir())),'Fresh output required.')
    require(not W.is_relative_to(Path('/home/codex/.codex/worktrees/ec20/Proofs'))and not W.is_relative_to(Path('/home/codex/src/Proofs')),'External output only.')
    tracked={}
    def pin(p,h):
        p=Path(p).resolve();require(p.is_file()and sha(p)==h,'Changed input '+str(p))
        require(str(p)not in tracked or tracked[str(p)]==h,'Conflicting identity.');tracked[str(p)]=h;return p
    for p,h in [(S,SOURCE_SHA),(A,AUDIT_SHA),(B,BOUNDARY_SHA),(Path(__file__),sha(__file__))]:pin(p,h)
    b=json.loads(B.read_text())
    for q in b['static_inputs']+[b['canonical_source']]:pin(q['path'],q['sha256'])
    require(b['source']['sha256']==SOURCE_SHA and b['audit']['sha256']==AUDIT_SHA and b['module']==MODULE,'Boundary identities.')
    require([p['record']['sha256']for p in b['parents']]==PARENT_SHAS,'Wrong two-parent identities.')
    parents=[];parent_paths=[];fresh_by_module={};inherited_by_module={}
    for spec in b['parents']:
        E=pin(spec['record']['path'],spec['record']['sha256']);e=json.loads(E.read_text());parents.append(e);parent_paths.append(dict(path=str(E),sha256=spec['record']['sha256']))
        require(e['status']=='PASS'and not e['prepare_only']and(e['named_axiom_probes'],e['callers'],e['warnings'])==(spec['probes'],spec['callers'],spec['warnings']),'Wrong actual parent outcome.')
        require(e['before']==e['after']and len(e['before'])==spec['inputs']and e['only_standard_axioms']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit'],'Incomplete parent.')
        require((e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[])and e['source_option_overrides']==e['audit_option_overrides']=={},'Parent limits changed.')
        require(not any(e[k]for k in ['compiler_version_query_performed','dependency_build','downloads']),'Parent execution scope changed.')
        require(e['source']['sha256']==spec['source_sha256']and e['audit']['sha256']==spec['audit_sha256'],'Parent source/audit identity.')
        for pp,hh in e['before'].items():pin(pp,hh)
        for k in ['source','audit']:pin(e[k]['path'],e[k]['sha256']);pin(e[k]['snapshot'],e[k]['sha256'])
        fs=e['fresh_modules'];require(len(fs)==1 and fs[0]['module']==spec['module'],'Wrong parent fresh module.')
        f=fs[0];pin(f['path'],f['sha256']);fresh_by_module[f['module']]=(e,f)
        require(e['source_object_recorded_before_audit']and e['source_pass_object']==dict(f,source_command_index=0)and e['fresh_first_provider_before_audit']=={k:f[k]for k in ['module','path','sha256']},'Parent fresh capture.')
        require(artifacts(f['path'])==e['source_pass_artifacts']and len(e['source_pass_artifacts'])==4,'Parent companion capture.')
        for x in e['source_pass_artifacts']:pin(x['path'],x['sha256'])
        require([c['label']for c in e['commands']]==['source','audit'],'Parent command order.')
        for c in e['commands']:
            log=pin(c['log'],c['log_sha256']);expect=[e['compiler']['path'],'-j1','-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if c['label']=='source'else[])+[e[c['label']]['snapshot']]
            require(c['command']==expect and c['exit_code']==0 and not c['timed_out']and c['interrupted']is None and c['seconds']>0 and log.read_text()==c['output'],'Parent raw command/log mismatch.')
        require(sum(c['seconds']for c in e['commands'])<=120 and sum(c['output'].count('warning:')for c in e['commands'])==spec['warnings'],'Parent budget/warning count.')
        ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        require(ns==spec['audit_names']and [x['name']for x in rr]==ns and rr==e['axiom_reports']and all(set(x['axioms'])<=STANDARD for x in rr),'Parent raw reports.')
        for q in e['reused_modules']+e['external_project_boundaries']:
            require(q['module']not in inherited_by_module or inherited_by_module[q['module']][1]==q,'Conflicting inherited pair.')
            inherited_by_module[q['module']]=(e,q)
    require(imports(S)==['Foundation.FirstOrder.SetTheory.Basic','Foundation.Vorspiel.ExistsUnique']and imports(A)==[MODULE]and S.read_text().startswith('module\n'),'Imports/header changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==12,'Audit census/names.')
    for q in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text()),'Untrusted proof exit.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text()),'Raised proof limits.')
    reused,external,tools=b['reused_modules'],b['external_project_boundaries'],b['toolchain_providers']
    require([q['module']for q in reused]==['Foundation.FirstOrder.SetTheory.Basic.Misc','Foundation.FirstOrder.SetTheory.Basic.Axioms','Foundation.FirstOrder.SetTheory.Basic.Model','Foundation.FirstOrder.SetTheory.Basic','Foundation.Vorspiel.ExistsUnique'],'Wrong fresh inherited subset.')
    require([q['module']for q in external]==['Foundation.FirstOrder.Completeness.CounterModel','Mathlib.SetTheory.Cardinal.Basic','Mathlib.Logic.IsEmpty'],'Wrong opaque cached boundary.')
    require([q['module']for q in tools]==['Init'],'Wrong tool boundary.')
    C=pin(b['compiler']['path'],b['compiler']['sha256'])
    require(all(b['compiler']==e['compiler']for e in parents),'Compiler changed.')
    for q in reused+external:
        if q['module']in fresh_by_module:
            e,f=fresh_by_module[q['module']]
            require((q['source'],q['source_sha256'],q['object'],q['object_sha256'],q['artifacts'])==(e['source']['path'],f['source_sha256'],f['path'],f['sha256'],e['source_pass_artifacts']),'Wrong new fresh pair.')
        else:
            e,old=inherited_by_module[q['module']];require(q==old,'Changed inherited pair.')
            for k in ['source','object']:require(e['before'][q[k]]==e['after'][q[k]]==q[k+'_sha256'],'Absent parent input.')
            oldfirst=next(x for x in e['actual_first_providers']if x['module']==q['module']);require(Path(oldfirst['actual_first']).resolve()==Path(q['object']).resolve()and oldfirst['sha256']==q['object_sha256'],'Parent selected first provider.')
        for k in ['source','object']:pin(q[k],q[k+'_sha256'])
        require(artifacts(q['object'])==q['artifacts'],'Changed companions.')
        for x in q['artifacts']:pin(x['path'],x['sha256'])
    require(all(tools==e['toolchain_providers']for e in parents),'Changed inherited tool boundary.')
    for q in tools:
        require(Path(q['object'])==C.parent.parent/'lib/lean'/rel(q['module']),'Tool root mismatch.')
        pin(q['object'],q['object_sha256']);require(artifacts(q['object'])==q['artifacts'],'Tool companion set.')
        for x in q['artifacts']:pin(x['path'],x['sha256'])
    projects={q['module']:q for q in reused};boundaries={q['module']:q for q in external};seen=set();seen_external=set()
    def visit(m):
        if m in boundaries:seen_external.add(m);return
        require(m in projects,'Unselected source import '+m)
        if m in seen:return
        seen.add(m)
        for n in imports(projects[m]['source']):visit(n)
    for m in imports(S):visit(m)
    require(seen==set(projects)and seen_external==set(boundaries),'Selected import DFS changed.')
    roots=[Path(x).resolve()for x in b['cached_roots']]
    require(all(b['cached_roots']==e['LEAN_PATH'].split(os.pathsep)[1:]for e in parents)and all(x.is_dir()for x in roots),'Cached root list changed.')
    require(all(not(x/rel(MODULE)).exists()for x in roots),'Unexpected preexisting target provider.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    # Lean chooses one root per namespace; preserve the opaque cached Foundation
    # branches while reserving exact selected artifacts and the fresh output.
    mirror_spec=b['namespace_mirror'];base=Path(mirror_spec['cached_tree']).resolve()
    require(mirror_spec['namespace']=='Foundation' and base==next(x/'Foundation'for x in roots if(x/'Foundation').is_dir()),'Wrong Foundation mirror root.')
    targets=[Path(m.replace('.','/')).relative_to('Foundation')for m in [q['module']for q in reused]+[MODULE]]
    mirror_links=[]
    def mirror(source,dest,relative=Path()):
        dest.mkdir(parents=True,exist_ok=True)
        for item in sorted(source.iterdir()):
            rp=relative/item.name;dd=dest/item.name
            if item.is_dir()and any(t.is_relative_to(rp)for t in targets):mirror(item,dd,rp)
            elif item.is_file()and any(rp.parent==t.parent and item.name.startswith(t.name+'.')for t in targets):continue
            else:
                dd.symlink_to(item.resolve(),target_is_directory=item.is_dir())
                mirror_links.append(dict(path=str(dd),target=str(item.resolve())))
    mirror(base,cache/'Foundation')
    for q in reused:
        for x in q['artifacts']:
            pp=Path(x['path']);dest=cache/rel(q['module']);dest=dest.parent/pp.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(pp)
    ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss);aa=snaps/'Audit.lean';shutil.copyfile(A,aa)
    pin(ss,SOURCE_SHA);pin(aa,AUDIT_SHA);toolroot=C.parent.parent/'lib/lean';search=[cache]+roots+[toolroot]
    def first(m):return next((r/rel(m)).resolve()for r in search if(r/rel(m)).is_file())
    def providers():
        rows=[]
        for q in reused+external+tools:
            pp=first(q['module']);require(pp==Path(q['object']).resolve()and sha(pp)==q['object_sha256'],'Wrong actual provider.')
            require(artifacts(pp)==q['artifacts'],'Selected companion drift.')
            rows.append(dict(module=q['module'],actual_first=str(pp),sha256=sha(pp)))
        return rows
    actual=providers();leanpath=os.pathsep.join(str(x)for x in [cache]+roots);env=dict(os.environ,LEAN_PATH=leanpath,LEAN_NUM_THREADS='1')
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope=b['scope'],source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=parent_paths,compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,external_project_boundaries=external,toolchain_providers=tools,actual_first_providers=actual,exact_selected_import_closure=sorted(seen),exact_selected_prerequisite_count=5,opaque_boundary_modules=sorted(seen_external),whole_namespace_cache_attested=False,source_option_overrides={},audit_option_overrides={},before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=leanpath,LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['legacy_scope'],namespace_mirrors=[dict(mirror_spec,scratch_tree=str(cache/'Foundation'))],namespace_mirror_links=mirror_links)
    def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
    def post():
        require(all(Path(q['path']).is_symlink()and str(Path(q['path']).resolve())==q['target']for q in mirror_links),'Namespace mirror changed.')
        r['after']={p:sha(p)for p in tracked};require(r['before']==r['after']and providers()==actual,'Postcheck failed.')
        for q in r['fresh_modules']:require(first(q['module'])==Path(q['path']).resolve()and sha(q['path'])==q['sha256'],'Fresh object changed.')
        if r['fresh_modules']:require(artifacts(r['fresh_modules'][0]['path'])==r['source_pass_artifacts'],'Fresh module companions changed.')
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
        r.update(fresh_modules=[q],source_pass_object=dict(q,source_command_index=0),source_object_recorded_before_audit=True,fresh_first_provider_before_audit=dict(module=MODULE,path=str(first(MODULE)),sha256=sha(first(MODULE))),source_pass_artifacts=artifacts(obj))
        require(first(MODULE)==obj.resolve()and len(r['source_pass_artifacts'])==4,'Fresh first provider/companion capture mismatch.');save()
        out=run('audit',aa);rr=reports(out);require([q['name']for q in rr]==[PREFIX+n for n in PROBES]and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong actual reports.')
        post();r.update(status='PASS',named_axiom_probes=12,callers=12,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(q['output'].count('warning:')for q in r['commands']))
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as ex2:r['postcheck_error']=repr(ex2)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
