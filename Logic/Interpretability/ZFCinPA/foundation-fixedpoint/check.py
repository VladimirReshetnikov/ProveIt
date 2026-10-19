#!/usr/bin/env python3
"""Fresh FixedPoint only; recorded Syntax and current-only arithmetic Model cached boundaries."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-foundation-fixedpoint')
MODULE='Foundation.FirstOrder.Bootstrapping.FixedPoint'
PREFIX='LO.FirstOrder.Arithmetic.'
PROBES=['Bootstrapping.Arithmetic.substNumeral_app_quote', 'Bootstrapping.Arithmetic.substNumerals_app_quote', 'Bootstrapping.Arithmetic.substNumerals_app_quote_quote', 'Bootstrapping.Arithmetic.substNumeralParams_app_quote', 'diagonal', 'multidiagonal', 'exclusiveMultifixedpoint_inj_iff', 'exclusiveMultidiagonal', 'multifixedpoint_pi', 'exclusiveMultifixedpoint_pi', 'parameterized_diagonal', 'parameterized_diagonal₁']
SOURCE_SHA='cdc2f381549c4e3bdb7d67a221d6a57217db4eb82793082e5df61a9e87c5280f'
AUDIT_SHA='5788a38164d703a7aca1213657953b3a61853e3234e85c400dc1dc55a3cf0343'
BOUNDARY_SHA='878ab7e4dae66cbe9f3762d3b225e1a64902a27cdc39e63a2c0bf066c1a18d29'
PARENT_SHA='c001333711a8ec93529f880e5586822e5c7e0bb142d699dc7e188aa260b65550'
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
    p.add_argument('--source',type=Path,default=HERE/'FixedPoint.lean');p.add_argument('--audit',type=Path,default=HERE/'Audit.lean')
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
    require(b['parent']['record']['sha256']==PARENT_SHA,'Wrong legacy parent identity.')
    spec=b['parent'];E=pin(spec['record']['path'],spec['record']['sha256']);pin(spec['original_record']['path'],spec['original_record']['sha256'])
    require(spec['record']['sha256']==spec['original_record']['sha256'],'Published/original record mismatch.')
    pin(spec['legacy_guard']['path'],spec['legacy_guard']['sha256']);e=json.loads(E.read_text());parent_paths=[dict(path=str(E),sha256=spec['record']['sha256'])]
    require(e['status']=='PASS'and(e['named_axiom_probes'],e['callers'],e['warnings'])==(15,15,0),'Wrong legacy outcome.')
    require(e['before']==e['after']and len(e['before'])==30 and all(e[k]for k in ['only_standard_axioms','all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit']),'Incomplete legacy record.')
    require(e['exact_project_import_closure']is True and not e['dependency_build']and not e['downloads'],'Legacy scope changed.')
    require(all(k not in e for k in ['source_pass_object','fresh_first_provider_before_audit','source_pass_artifacts','shared_timeout_seconds','source_object_recorded_before_audit']),'Invented legacy captures.')
    for k in ['source','audit']:
        require(e[k]==spec[k],'Legacy snapshot identity.');pin(e[k]['snapshot'],e[k]['sha256'])
    require([c['label']for c in e['commands']]==['source','audit'],'Legacy command order.')
    require(len(e['fresh_modules'])==1,'Legacy target census.');f=e['fresh_modules'][0]
    for c in e['commands']:
        log=pin(spec['logs'][c['label']]['path'],spec['logs'][c['label']]['sha256'])
        expected=[e['compiler']['path'],'-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if c['label']=='source'else[])+[e[c['label']]['snapshot']]
        require(c['command']==expected and c['exit_code']==0 and c['seconds']>0 and log.read_text()==c['output']and 'warning:'not in c['output'],'Legacy raw command/log mismatch.')
        require(not any(k in c for k in ['timed_out','interrupted','log_sha256']),'Legacy absent-field schema changed.')
    ns=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
    require(ns==spec['audit_names']and len(ns)==15 and [q['name']for q in rr]==ns and all(set(q['axioms'])<=STANDARD for q in rr),'Legacy raw reports.')
    require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==15,'Legacy typed callers.')
    require(imports(S)==['Foundation.FirstOrder.Arithmetic.Basic.Model','Foundation.FirstOrder.Bootstrapping.Syntax']and imports(A)==[MODULE]and S.read_text().startswith('module\n'),'Imports/header changed.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==12,'Audit census/names.')
    for q in [S,A]:
        require(not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text()),'Untrusted proof exit.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text()),'Raised proof limits.')
    reused,external,tools=b['reused_modules'],b['external_project_boundaries'],b['toolchain_providers']
    require(reused==[] and [q['module']for q in external]==['Foundation.FirstOrder.Arithmetic.Basic.Model','Foundation.FirstOrder.Bootstrapping.Syntax'],'Wrong opaque cached boundaries.')
    require([q['module']for q in tools]==['Init'],'Wrong tool boundary.')
    C=pin(b['compiler']['path'],b['compiler']['sha256'])
    require({k:b['compiler'][k]for k in ['path','sha256','version']}==e['compiler']and b['compiler']['compiler_version_query_performed']is False,'Compiler identity changed.')
    for q in external:
        if q['module']=='Foundation.FirstOrder.Bootstrapping.Syntax':
            old=next(x for x in e['providers']if x['module']==q['module']);require(q['historical_pair']==old and old['actual_first_provider']is True,'Wrong recorded Syntax boundary.')
            for k in ['source','object']:
                require(q[k]==old[k]and q[k+'_sha256']==old[k+'_sha256']and e['before'].get(q[k])==e['after'].get(q[k])==q[k+'_sha256'],'Absent recorded Syntax pair.')
        else:require(q['status']=='CURRENT_ONLY_OPAQUE_CACHED_BOUNDARY','Model provenance overstated.')
        for k in ['source','object']:pin(q[k],q[k+'_sha256'])
        require(artifacts(q['object'])==q['artifacts']and len(q['artifacts'])==4,'Changed boundary companions.')
        for x in q['artifacts']:pin(x['path'],x['sha256'])
    for q in tools:
        require(Path(q['object'])==C.parent.parent/'lib/lean'/rel(q['module']),'Tool root mismatch.')
        pin(q['object'],q['object_sha256']);require(artifacts(q['object'])==q['artifacts']and len(q['artifacts'])==4,'Tool companion set.')
        for x in q['artifacts']:pin(x['path'],x['sha256'])
    excluded=b['excluded_cached_target'];require(excluded['module']==MODULE,'Wrong excluded cached target.')
    for x in excluded['companions']:pin(x['path'],x['sha256'])
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
    require(b['cached_roots']==e['LEAN_PATH'].split(os.pathsep)[1:]and all(x.is_dir()for x in roots),'Cached root list changed.')
    require([(x/rel(MODULE)).resolve()for x in roots if(x/rel(MODULE)).is_file()]==[Path(excluded['object']['path']).resolve()],'Unexpected cached target provider; the one pinned old target will be excluded from the first namespace mirror.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    # Lean chooses one root per namespace; preserve the opaque cached Foundation
    # branches while reserving exact selected artifacts and the fresh output.
    mirror_spec=b['namespace_mirror'];base=Path(mirror_spec['cached_tree']).resolve()
    require(mirror_spec['namespace']=='Foundation' and base==next(x/'Foundation'for x in roots if(x/'Foundation').is_dir()),'Wrong Foundation mirror root.')
    targets=[Path(m.replace('.','/')).relative_to('Foundation')for m in [q['module']for q in reused+external if q['module'].startswith('Foundation.')]+[MODULE]]
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
    for q in reused+external:
        for x in q['artifacts']:
            pp=Path(x['path']);dest=cache/rel(q['module']);dest=dest.parent/pp.name;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(pp)
    require(not any((cache/rel(MODULE)).parent.glob((cache/rel(MODULE)).stem+'.*')),'Old target companion leaked into fresh namespace.')
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
    r=dict(status='PREPARED_NOT_BUILT'if a.prepare_only else'RUNNING',prepare_only=a.prepare_only,scope=b['scope'],source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=parent_paths,compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,external_project_boundaries=external,toolchain_providers=tools,actual_first_providers=actual,exact_selected_import_closure=sorted(seen),exact_selected_prerequisite_count=0,opaque_boundary_modules=sorted(seen_external),whole_namespace_cache_attested=False,source_option_overrides={},audit_option_overrides={},before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=leanpath,LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,parent_scope=b['legacy_scope'],namespace_mirrors=[dict(mirror_spec,scratch_tree=str(cache/'Foundation'))],namespace_mirror_links=mirror_links)
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
