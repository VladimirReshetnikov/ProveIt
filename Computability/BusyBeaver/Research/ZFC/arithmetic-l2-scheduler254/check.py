#!/usr/bin/env python3
"""Internal dag254 scheduler root step:2 probes/2 callers,79 projects,3 cache boundaries.
Shared120s, -j1 -M4096; preserved source8192/300000, default audit; no rebuild/version query/download.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-w3w4w5-fresh-check-plan/v2/arithmetic-l2-scheduler254')
MODULE='BusyBeaver.ZFC.ArithmeticL2Scheduler254'
SOURCE_SHA='288a5bd9bfb7aa5b888eca7b766b354f3ee8329fad47eecdb73308c063c881c5'
AUDIT_SHA='9b41aad08fd53b8daf56c3efb105fc4b15a547fd3a1fbabbf7ad3499a5750301'
BOUNDARY_SHA='267de88611f8bb62b65a2eb6dfba7a736927571da7ecf66686cc14d22fceace8'
PARENT_PINS={'root': '6d65c3f1506dcfe4fc69593b12fd89048cc7bec4dddb118e1097660050fa6393', 'seed': 'c17ddc2ab44d328e3a3cb70ccea114d77d6732534e399456d352510e593ccbf8', 'positive': 'a13e02b88a5012f4c11590998605d75eac8f735cf57e44d10781f93700dab8ba'}
PARENT_CENSUS={'root': (4, 4, 819), 'seed': (10, 11, 122), 'positive': (4, 4, 39)}
PARENT_SCHEMAS={'root': 'modern_arithmetic', 'seed': 'seed_shared120_v1', 'positive': 'positive_legacy_v1'}
PROBES=['reads_halt', 'root_step']
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticL2.'
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(x,msg):
    if not x:raise RuntimeError(msg)
def rel(m,suffix='.olean'):return Path(m.replace('.','/')).with_suffix(suffix)
def imports(p):return re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def reports(text):
    rr=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in rr]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'ArithmeticL2Scheduler254.lean')
    p.add_argument('--audit',type=Path,default=HERE/'Audit.lean');p.add_argument('--boundary',type=Path,default=Path(__file__).resolve().with_name('boundary.json'))
    p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');args=p.parse_args()
    require(__debug__,'No optimized Python.');require(not BOUNDARY_SHA.startswith('PENDING_'),'Freeze the actual selected-provider boundary first.');S,A,B,W=args.source.resolve(),args.audit.resolve(),args.boundary.resolve(),args.output.resolve()
    require(not W.exists()or(W.is_dir()and not any(W.iterdir())),'Fresh output required.')
    require(all(not W.is_relative_to(Path(root))for root in ['/home/codex/.codex/worktrees/ec20/Proofs','/home/codex/src/Proofs']),'External output required.')
    tracked={}
    def pin(path,h):
        q=Path(path).resolve();require(q.is_file()and sha(q)==h,'Changed input '+str(q));require(str(q)not in tracked or tracked[str(q)]==h,'Conflicting input pin.');tracked[str(q)]=h;return q
    for q,h in [(S,SOURCE_SHA),(A,AUDIT_SHA),(B,BOUNDARY_SHA),(Path(__file__),sha(__file__))]:pin(q,h)
    b=json.loads(B.read_text());C=pin(b['compiler']['path'],b['compiler']['sha256'])
    for d in b['static_inputs']:pin(d['path'],d['sha256'])
    require({x['label']:x['record']['sha256']for x in b['parents']}==PARENT_PINS,'Wrong actual parent pins.')
    pool={};externals={};toolpool={};parents={};evidence=[]
    for spec in b['parents']:
        label=spec['label'];E=pin(spec['record']['path'],PARENT_PINS[label]);e=json.loads(E.read_text());parents[label]=e;evidence.append(dict(path=str(E),sha256=PARENT_PINS[label]))
        if spec['schema']in ('seed_shared120_v1','positive_legacy_v1'):
            seed=spec['schema']=='seed_shared120_v1'
            require(label==('seed'if seed else'positive')and PARENT_SCHEMAS[label]==spec['schema'],'Wrong historical schema label.')
            require(e['status']=='PASS'and(e['named_axiom_probes'],e['callers'],len(e['before']))==PARENT_CENSUS[label]==(spec['probes'],spec['callers'],spec['before_inputs']),'Wrong historical actual census.')
            require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete historical postchecks.')
            for path,h in e['before'].items():pin(path,h)
            require(e['compiler']['path']==str(C)and e['compiler']['sha256']==b['compiler']['sha256']and not e['dependency_build']and not e['downloads'],'Wrong historical compiler/dependency scope.')
            require(e['exact_project_import_closure']is True and len(e['reused_modules'])==(48 if seed else 11),'Wrong historical Boolean closure/census.')
            require(e['dependencies']['root']==b['dependencies']['root']and e['dependencies']['lake_manifest_sha256']==b['dependencies']['lake_manifest_sha256']and e['LEAN_PATH'].split(os.pathsep)[1:]==b['libraries'],'Wrong historical dependency/libraries.')
            for dep in ('Foundation','Mathlib'):
                require(all(e['dependencies'][dep][k]==b['dependencies'][dep][k]for k in ('path','pin','tracked_clean'))and e['dependencies'][dep]['tracked_clean'],'Wrong historical dependency '+dep)
            for key in ('source_option_overrides','audit_option_overrides','shared_timeout_seconds','LEAN_NUM_THREADS','global_option_overrides','compiler_version_query_performed'):
                require(key not in e,'Unexpected historical top-level policy '+key)
            for role in ('source','audit'):
                require(e[role]['sha256']==spec[role+'_sha256'],'Wrong historical source/audit.');pin(e[role]['path'],e[role]['sha256']);pin(e[role]['snapshot'],e[role]['sha256'])
            require(re.findall(r'^set_option .*$',Path(e['source']['snapshot']).read_text(),re.M)==spec['source_options']and not re.findall(r'^set_option .*$',Path(e['audit']['snapshot']).read_text(),re.M),'Changed historical source/audit options.')
            f,=e['fresh_modules'];pin(f['path'],f['sha256'])
            require(f['module']==spec['module']and f['source_sha256']==e['source']['sha256']and f['sha256']==spec['fresh_object_sha256'],'Wrong historical fresh object.')
            if seed:
                require(e['prepare_only']is False and e['warnings']=={'source':0,'audit':0}and e['compiler']['compiler_version_query_performed']is False,'Wrong Seed actual/version/warnings schema.')
                require((e['per_command_timeout_seconds'],e['shared_wall_seconds'])==(120,120)and e['limits']=={'threads':1,'memory_mebibytes':4096,'proof_limits':'Lean defaults for new source/audit','shared_source_audit_seconds':120},'Wrong Seed shared execution policy.')
                require((e['project_module_count'],e['external_boundary_count'],e['input_count'])==(48,3,122),'Wrong Seed census.')
                require(e['source_object_recorded_before_audit']and e['source_pass_object']==dict(f,source_command_index=0)and e['fresh_first_provider_before_audit']=={k:f[k]for k in ('module','path','sha256')},'Wrong Seed pre-audit captures.')
            else:
                require(e['warnings']==0 and e['memory_limit_mib']==4096 and e['reused_count']==11 and e['source_override']and e['audit_override'],'Wrong Positive legacy policy.')
                for key in ('prepare_only','source_pass_object','source_object_recorded_before_audit','fresh_first_provider_before_audit','toolchain_providers','actual_first_providers','per_command_timeout_seconds','shared_wall_seconds','limits'):
                    require(key not in e,'Invented modern Positive metadata '+key)
                require('compiler_version_query_performed'not in e['compiler'],'Wrong legacy compiler schema.')
            require([c['label']for c in e['commands']]==['source','audit'],'Wrong historical command order.')
            for c in e['commands']:
                expected=[str(C)]+(['-j1']if seed else[])+['-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if c['label']=='source'else[])+[e[c['label']]['snapshot']]
                require(c['command']==expected and c['exit_code']==0,'Historical source/audit failure or changed arguments.')
                require(all(k not in c for k in ('log','log_sha256','interrupted'))and(c.get('timed_out')is False if seed else'timed_out'not in c),'Wrong historical command schema.')
                log=pin(E.parent/(c['label']+'.log'),hashlib.sha256(c['output'].encode()).hexdigest());require(log.read_text()==c['output'],'Changed historical raw log.')
                require(not any(x in c['output']for x in ('error:','warning:','sorryAx')),'Unexpected historical diagnostic.')
            an=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
            recorded=[dict(name=q['theorem'],axioms=sorted(q['axioms']))for q in e['actual_axiom_sets'if seed else'axiom_reports']]
            require(len(an)==spec['probes']and an==[q['name']for q in rr]and rr==recorded and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong historical ordered raw reports.')
            require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==spec['callers'],'Wrong historical typed callers.')
            oldroots=[Path(x)for x in e['LEAN_PATH'].split(os.pathsep)]+[C.parent.parent/'lib/lean']
            oldfirst={q['module']:q for q in e['actual_first_providers'if seed else'actual_project_providers']}
            ep=e['providers'];expectedfirst={q['module']for q in e['reused_modules']+(ep if seed else[])}
            require(len(oldfirst)==len(e['actual_first_providers'if seed else'actual_project_providers'])and set(oldfirst)==expectedfirst,'Wrong historical first census.')
            for q in e['reused_modules']+ep:
                for k in ('source','object'):
                    pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==q[k+'_sha256'],'Historical pair not bound in before.')
                resolved=next((r/rel(q['module'])for r in oldroots if(r/rel(q['module'])).is_file()),None)
                require(resolved is not None and resolved.resolve()==Path(q['object']).resolve(),'Changed historical first provider.')
                if q['module']in oldfirst:
                    old=oldfirst[q['module']];oldpath=old['actual_first']if seed else old['path']
                    require(Path(oldpath).resolve()==Path(old['resolved']).resolve()==resolved.resolve()and old['sha256']==q['object_sha256'],'Wrong recorded historical first provider.')
                    if not seed:require(old['actual_first_provider']is True,'Wrong Positive first-provider flag.')
                else:require(q['actual_first_provider']is True,'Wrong Positive external first-provider flag.')
            require({q['module']for q in ep}==set(b['direct_external_boundaries'])|(set()if seed else{'Foundation.FirstOrder.Arithmetic.HFS.Seq'}),'Wrong historical external boundary.')
            if seed:
                require(e['actual_direct_tool_imports']==['Init']and e['inherited_additional_toolchain_boundary']=='Lean.Elab.Tactic.Omega','Wrong historical tool scope.')
                require({q['module']for q in e['toolchain_providers']}==set(toolpool),'Wrong Seed tools.')
                for q in e['toolchain_providers']:
                    pin(q['object'],q['object_sha256']);pin(q['toolchain_reference'],q['toolchain_reference_sha256'])
                    require(q['actual_first_provider']and Path(q['actual_first']).resolve()==Path(q['object']).resolve()and q['object_sha256']==toolpool[q['module']]['object_sha256']==q['toolchain_reference_sha256'],'Wrong Seed tool identity.')
            else:
                require({q['module']for q in e['direct_external_providers']}==set(b['direct_external_boundaries']),'Wrong Positive direct externals.')
                for q in e['direct_external_providers']:require(q in ep,'Unlisted Positive direct external.')
            for q in ep:
                if q['module']in externals:require(all(externals[q['module']][k]==q[k]for k in ('source_sha256','object','object_sha256')),'Conflicting historical external pair.')
                else:externals[q['module']]=q
            observed=[]
            for q in e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]:
                if q['module']in pool:
                    chosen=pool[q['module']];require(chosen['source_sha256']==q['source_sha256'],'Conflicting historical source.')
                    if chosen['object_sha256']!=q['object_sha256']:observed.append(dict(parent=label,module=q['module'],selected=chosen,historical=q))
                else:pool[q['module']]=q
            require(observed==[q for q in b['same_source_object_alternatives']if q['parent']==label]and[q['module']for q in observed]==['BusyBeaver.ZFC.ArithmeticCantor'],'Unlisted historical object alternative.')
            continue
        require(label in PARENT_SCHEMAS and spec['schema']==PARENT_SCHEMAS[label],'Wrong explicit parent schema.')
        require(e['status']=='PASS'and e['prepare_only']is False and(e['named_axiom_probes'],e['callers'])==(spec['probes'],spec['callers'])==PARENT_CENSUS[label][:2],'Wrong actual parent.')
        require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete parent.')
        require(len(e['before'])==spec['before_inputs']==PARENT_CENSUS[label][2],'Wrong parent input census.')
        for path,h in e['before'].items():pin(path,h)
        require(e['compiler']==b['compiler']and not e['dependency_build']and not e['downloads']and not e['compiler'].get('compiler_version_query_performed',False),'Different compiler/execution scope.')
        require((e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'],e['warnings'])==(120,4096,'1',[],0)and not e['compiler_version_query_performed'],'Wrong modern policy.')
        if spec['schema']=='modern_arithmetic':
            require(e['dependencies']==b['dependencies']and e['LEAN_PATH'].split(os.pathsep)[1:]==b['libraries'],'Changed arithmetic dependency metadata/libraries.')
        else:
            require('dependencies'not in e and not e.get('providers',[])and len(e['LEAN_PATH'].split(os.pathsep))==1,'Wrong Core-only parent schema.')
        for role in ('source','audit'):
            require(e[role]['sha256']==spec[role+'_sha256'],'Wrong parent source/audit.');pin(e[role]['path'],e[role]['sha256']);pin(e[role]['snapshot'],e[role]['sha256'])
        require(re.findall(r'^set_option .*$',Path(e['source']['snapshot']).read_text(),re.M)==spec['source_options'],'Changed disclosed parent source options.')
        f,=e['fresh_modules'];pin(f['path'],f['sha256'])
        require(f['module']==spec['module']and f['source_sha256']==e['source']['sha256']and f['sha256']==spec['fresh_object_sha256'],'Wrong parent fresh object.')
        require(e['source_object_recorded_before_audit']and e['source_pass_object']==dict(f,source_command_index=0),'Missing source-pass capture.')
        require(e['fresh_first_provider_before_audit']=={k:f[k]for k in ('module','path','sha256')},'Wrong pre-audit first capture.')
        require([c['label']for c in e['commands']]==['source','audit'],'Parent command order.')
        for c in e['commands']:
            require(c['exit_code']==0 and c['timed_out']is False and c.get('interrupted')is None,'Parent command failure.')
            expected=[str(C),'-j1','-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if c['label']=='source'else[])+[e[c['label']]['snapshot']]
            require(c['command']==expected,'Wrong parent arguments.')
            log=Path(c['log']);pin(log,hashlib.sha256(c['output'].encode()).hexdigest())
            require(log.read_text()==c['output']and(sha(log)==c['log_sha256']),'Changed raw parent log.')
            require(not any(x in c['output']for x in ('error:','warning:','sorryAx')),'Unexpected parent diagnostic.')
        an=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        recorded=e['axiom_reports']
        require(len(an)==spec['probes']and an==[x['name']for x in rr]and rr==recorded and all(set(x['axioms'])<=STANDARD for x in rr),'Wrong parent raw reports.')
        require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==spec['callers'],'Wrong parent callers.')
        ep=e.get('providers',[]);old_first={q['module']:q for q in e['actual_first_providers']};oldroots=[Path(q)for q in e['LEAN_PATH'].split(os.pathsep)]+[C.parent.parent/'lib/lean']
        expectedfirst={q['module']for q in e['reused_modules']+ep+e['toolchain_providers']}
        require(len(old_first)==len(e['actual_first_providers'])and set(old_first)==expectedfirst,'Wrong historical first census.')
        for q in e['reused_modules']+ep+e['toolchain_providers']:
            for k in ('source','object'):
                if k in q:pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==q[k+'_sha256'],'Unbound historical provider.')
            first_old=next((root/rel(q['module'])).resolve()for root in oldroots if(root/rel(q['module'])).is_file())
            require(first_old==Path(q['object']).resolve(),'Changed parent first provider.')
            captured=old_first.get(q['module'],q);require(Path(captured['actual_first']).resolve()==first_old and captured.get('sha256',captured.get('object_sha256'))==q['object_sha256'],'Wrong historical first capture.')
        for q in e['reused_modules']+[dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])]:
            if q['module']in pool:require(all(pool[q['module']][k]==q[k]for k in ('source_sha256','object_sha256')),'Conflicting project source/object.')
            else:pool[q['module']]=q
        for q in ep:
            if q['module']in externals:require(q==externals[q['module']],'Conflicting external pair.')
            else:externals[q['module']]=q
        for q in e['toolchain_providers']:
            if q['module']in toolpool:require(toolpool[q['module']]['object_sha256']==q['object_sha256'],'Conflicting tool.')
            else:toolpool[q['module']]=q
    reused=b['reused_modules'];providers=b['providers'];tools=b['toolchain_providers'];selected={q['module']:q for q in reused};external={q['module']for q in providers};seen=set();found=set();toolnames={'Init'}
    require(len(selected)==len(reused)==79 and external==set(b['direct_external_boundaries'])and external<=set(externals)and len(external)==3,'Wrong selected boundary.')
    require(providers==[q for q in parents['root']['providers']if q['module']in external]and tools==parents['root']['toolchain_providers'],'Changed external/tool selection.')
    for q in reused:
        require(q['module']in pool and all(q[k]==pool[q['module']][k]for k in ('source_sha256','object_sha256','object')),'Selected pair absent from actual parents.')
        for k in ('source','object'):pin(q[k],q[k+'_sha256'])
    def visit(m):
        if m in {'Init','Lean.Elab.Tactic.Omega'}:toolnames.add(m);return
        if m in external:found.add(m);return
        require(m in selected,'Unselected project import '+m)
        if m in seen:return
        seen.add(m)
        for c in imports(selected[m]['source']):visit(c)
    require(imports(S)==['BusyBeaver.ZFC.ArithmeticL2Root254', 'BusyBeaver.ZFC.ArithmeticEnumeratorSeed246', 'BusyBeaver.ZFC.ArithmeticPositiveSimulation254']and imports(A)==[MODULE],'Wrong source imports.')
    for m in imports(S):visit(m)
    require(seen==set(selected)==set(b['expected_projects'])and found==external and toolnames=={q['module']for q in tools},'Wrong exact import DFS.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==2,'Wrong2/2 audit.')
    for q in (S,A):require(not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text()),'Untrusted shortcut.')
    require(re.findall(r'^set_option .*$',S.read_text(),re.M)==['set_option autoImplicit false', 'set_option maxRecDepth 8192', 'set_option maxHeartbeats 300000']and not re.findall(r'^set_option .*$',A.read_text(),re.M),'Changed explicit source/audit option policy.')
    require(b['dependencies']==parents['root']['dependencies'],'Wrong dependency metadata.');D=Path(b['dependencies']['root']);pin(D/'lake-manifest.json',b['dependencies']['lake_manifest_sha256'])
    def dependency_state():
        state={}
        for name in ('Foundation','Mathlib'):
            d=b['dependencies'][name];root=Path(d['path']);head=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip();dirty=subprocess.check_output(['git','-C',str(root),'status','--porcelain','--untracked-files=no'],text=True)
            require(head==d['pin']and d['tracked_clean']and not dirty,'Changed dependency '+name);state[name]=dict(pin=head,tracked_clean=True)
        return state
    dep_state=dependency_state();libs=[Path(x)for x in b['libraries']]
    require(b['libraries']==parents['root']['LEAN_PATH'].split(os.pathsep)[1:]and all(x.is_dir()for x in libs),'Wrong existing library roots.')
    W.mkdir(parents=True,exist_ok=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    for q in reused:
        dst=cache/rel(q['module']);dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(Path(q['object']).resolve())
    ss=snaps/rel(MODULE,'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss);aa=snaps/'Audit.lean';shutil.copyfile(A,aa);pin(ss,SOURCE_SHA);pin(aa,AUDIT_SHA)
    search=[cache,*libs,C.parent.parent/'lib/lean']
    def first(m):
        q=next((root/rel(m)for root in search if(root/rel(m)).is_file()),None);require(q is not None,'Missing provider '+m);return q.resolve()
    def provider_check():
        rows=[]
        for q in reused+providers+tools:
            pp=first(q['module']);require(pp==Path(q['object']).resolve()and sha(pp)==q['object_sha256'],'Wrong actual first provider '+q['module']);rows.append(dict(module=q['module'],actual_first=str(pp),sha256=sha(pp)))
        return rows
    actual=provider_check();env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
    record=dict(status='PREPARED_NOT_BUILT'if args.prepare_only else'RUNNING',prepare_only=args.prepare_only,scope='One exact dag254 root invocation implements one represented scheduler step in arbitrary ISigma1 models: it halts on absorbing zero or exits at the next live record with candidate pointer decreasing or next candidate incrementing. command_step and reads_halt preserve their explicit premises. Catalogue occurrence, positive-clock iteration, logical seed equivalence and binary consistency belong to later modules.',source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=evidence,parent_scope=b['scope'],compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,providers=providers,toolchain_providers=tools,actual_first_providers=actual,exact_project_prerequisite_count=79,exact_project_import_closure=sorted(seen),direct_external_boundaries=sorted(external),dependencies=b['dependencies'],before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],source_option_overrides=dict(maxRecDepth=8192,maxHeartbeats=300000),audit_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
    def save():(W/'verification.json').write_text(json.dumps(record,ensure_ascii=False,indent=2)+'\n')
    def post():
        record['after']={q:sha(q)for q in tracked};require(record['after']==record['before'],'Input changed during check.')
        require(provider_check()==actual and dependency_state()==dep_state,'Provider/dependency postcheck failed.')
        for q in record['fresh_modules']:require(first(q['module'])==Path(q['path']).resolve()and sha(q['path'])==q['sha256'],'Fresh object/first provider changed.')
        record['all_input_provider_postchecks']=True
    save()
    try:
        if args.prepare_only:post();save();print(W/'verification.json');return
        deadline=time.monotonic()+120
        def run(label,file,obj=None):
            remaining=deadline-time.monotonic();require(remaining>0,'Shared deadline exhausted.')
            cmd=[str(C),'-j1','-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)]
            started=time.monotonic();proc=subprocess.Popen(cmd,cwd=snaps,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
            timed_out=False;interrupted=None
            try:data,_=proc.communicate(timeout=remaining)
            except BaseException as ex:
                timed_out=isinstance(ex,subprocess.TimeoutExpired);interrupted=None if timed_out else type(ex).__name__
                try:os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                data,_=proc.communicate()
            out=data.decode(errors='replace');log=W/(label+'.log');log.write_text(out)
            record['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-started,exit_code=proc.returncode,timed_out=timed_out,interrupted=interrupted,output=out,log=str(log),log_sha256=sha(log)))
            save();require(not timed_out and interrupted is None and proc.returncode==0,label+' failed; exact log preserved.')
            require('sorryAx'not in out and "declaration uses 'sorry'"not in out,'Untrusted declaration in output.');return out
        obj=cache/rel(MODULE);require(not obj.exists(),'Fresh target already present.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)
        fresh=dict(module=MODULE,path=str(obj),sha256=sha(obj),source_sha256=SOURCE_SHA);record['fresh_modules']=[fresh];record['source_pass_object']=dict(fresh,source_command_index=0)
        require(first(MODULE)==obj.resolve(),'Fresh source object is not first provider.');record['fresh_first_provider_before_audit']=dict(module=MODULE,path=str(first(MODULE)),sha256=sha(first(MODULE)));record['source_object_recorded_before_audit']=True;save()
        out=run('audit',aa);rr=reports(out);require([q['name']for q in rr]==[PREFIX+n for n in PROBES],'Wrong ordered actual axiom reports.');require(all(set(q['axioms'])<=STANDARD for q in rr),'Nonstandard axiom report.')
        post();record.update(status='PASS',named_axiom_probes=2,callers=2,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(c['output'].count('warning:')for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as post_error:record['postcheck_error']=repr(post_error)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
