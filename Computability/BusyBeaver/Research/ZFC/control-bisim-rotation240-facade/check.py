#!/usr/bin/env python3
"""Final packed-control facade:8 probes/10 callers,70 prospective projects,3 cache boundaries.
Shared120s, -j1 -M4096; inherited source100000/unlimited-heartbeats, default audit; no rebuild/version query/download.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-w3-control-bisim-split-generated1/facade')
MODULE='BusyBeaver.ZFC.ControlBisimRotation240'
SOURCE_SHA='6bdfc3ed2c463d3280098e6559e02cbee7bfe6155d00967fb7641a5f9d51a530'
AUDIT_SHA='15a9d29a0538d8b54ba64d2be3e8de8cb38e451e0dd751934d8ca747774fe67f'
BOUNDARY_SHA='79623983b5c8c3f20f5db0c0d2c6f45a3166ae6969f5d7e9ff6b063dd58887bf'
PARENT_PINS={'leaf000': 'bafb7c26397e3e03104ca6c2687106d3762a8dfebdc7559e2229c39c763055bc', 'leaf001': 'e0e7b620e9f82918ae0691cc35d3a0d5ac55ac3387078ca1c4e80673dea1c1d8', 'leaf002': 'bc9bc9f04bb4a5263e038225481985057ad95c5f127d965b614adffaeddef83f', 'leaf003': '53c3e093306528065031beda4d9b37de39b7b5dc25610e9fb62851e009c9faf6', 'leaf004': 'b9e3106c5eb03f202c37ef73a602667d3ff8459d67097f0e48902d81a12ad856', 'leaf005': '3fd556618ceb43dcf53ca81b5a6273440c9ec9b20c02d4bda08451d7479bcb75', 'leaf006': 'f5e9cb10f52fca5b12d04dc0ac1931c78516c96212a92a9f3bf449efbe2c334d', 'leaf007': 'a6e0fa808ef8c23beacabffda5b383dd239331fe1f4434196c1e2647ddbd01c3', 'leaf008': '71f97320e146036aff517e1738dd5731124ac29d5c4ed6f8e357eecb16d50e98', 'leaf009': '8a1efa6acce831c616bdb7e36bd8a647679d22d6bdf22879b76b7510a8746ff1', 'leaf010': 'a06066451653cbd209ac963d7cb9172a3bb7ca719cfd642a5c5d9da5f7ad7b8a', 'leaf011': '794cf8c2b9cbb30f75e605353463d20a623175549d1432df265665e1644cdc4d', 'leaf012': '49c4c595fb2c6710092386d20125a40aa2c131ec15b4eeb13358fe5036042da2', 'leaf013': '8d0ef11244b71fc7863291dc4297371909da9617aaa2f53363a9ec382331f2f7', 'leaf014': '8509de071ab88d163d2cb22f9eac402e63b6ddd40f4836f7185742c1f05a385d', 'leaf015': 'fb1e32c41c736191fa578ddc26ed1f4835b43052d0951040076326d7ff3e5d92', 'leaf016': '38e1d9f5c4a4c4eefef5780cb1ddaae3770aba834499a7f654d08cde0dbbc534', 'leaf017': '21ea5ef70c81347a899a5b63faa7160b21e5f5191f61f4e01bf445610d618801', 'leaf018': '097779afe3719158b981bcd67c8a5bf8447ce39460763ca2218ff88efd8421ce', 'leaf019': '1b2766a560ed8fdb65a5ddeae87d7e505ee2c97d752ba3b3f568363339638f2f', 'leaf020': '686971e6a2c021fc08db4e7404f52b37b41f2a66ae5d90e4fe2e2b62bc5f4c35', 'leaf021': '727d5b35123f716115aaabbb625b1929b63ae1e5e6f19221b43ffca8a69e93f6', 'leaf022': 'bb3b813fa0665778004ad80f1641ca885c1b75ce725abe733aec27d7e0a2f28f', 'leaf023': '3d76bedb7bb9f68eca59e2c4b5a960acfb5dc814ff8adeb7932af681b753deff', 'leaf024': 'd989be8a17efa4a30e6d8e81bcd941f67f2a641df407d8ff722b69c40faf2eab', 'leaf025': 'daf079093276a6be5c3d5b5d616a8d5669da45a63c60c91e15c2c8f6790e2695', 'leaf026': '136515b3304d3629d4e5c8d01204dd01067f0ecc95954264916daf40469dae8b', 'leaf027': 'ab3866bce3304aadd5257f2a1ff05db3ead2d8606587d6225c62b1693af41953', 'leaf028': 'c5576b0bab3539e95210d232872a6075f010df049954e540525b0a676f4efa4a', 'leaf029': 'ecdcc7c242a1cf57853d1c5c46e12d0329400fa86cc425f2e7da5e6a9df762ad', 'leaf030': '6800e417b1d5fea5211ccb35e9cd2e927be370c70b4c1f89c9c71ddcc32cd648'}
PARENT_CENSUS={'leaf000': (1, 1, 717), 'leaf001': (1, 1, 724), 'leaf002': (1, 1, 724), 'leaf003': (1, 1, 724), 'leaf004': (1, 1, 724), 'leaf005': (1, 1, 724), 'leaf006': (1, 1, 724), 'leaf007': (1, 1, 724), 'leaf008': (1, 1, 724), 'leaf009': (1, 1, 724), 'leaf010': (1, 1, 724), 'leaf011': (1, 1, 724), 'leaf012': (1, 1, 724), 'leaf013': (1, 1, 724), 'leaf014': (1, 1, 724), 'leaf015': (1, 1, 724), 'leaf016': (1, 1, 724), 'leaf017': (1, 1, 724), 'leaf018': (1, 1, 724), 'leaf019': (1, 1, 724), 'leaf020': (1, 1, 724), 'leaf021': (1, 1, 724), 'leaf022': (1, 1, 724), 'leaf023': (1, 1, 724), 'leaf024': (1, 1, 724), 'leaf025': (1, 1, 724), 'leaf026': (1, 1, 724), 'leaf027': (1, 1, 724), 'leaf028': (1, 1, 724), 'leaf029': (1, 1, 724), 'leaf030': (1, 1, 724)}
PARENT_SCHEMAS={'leaf000': 'modern_arithmetic', 'leaf001': 'modern_arithmetic', 'leaf002': 'modern_arithmetic', 'leaf003': 'modern_arithmetic', 'leaf004': 'modern_arithmetic', 'leaf005': 'modern_arithmetic', 'leaf006': 'modern_arithmetic', 'leaf007': 'modern_arithmetic', 'leaf008': 'modern_arithmetic', 'leaf009': 'modern_arithmetic', 'leaf010': 'modern_arithmetic', 'leaf011': 'modern_arithmetic', 'leaf012': 'modern_arithmetic', 'leaf013': 'modern_arithmetic', 'leaf014': 'modern_arithmetic', 'leaf015': 'modern_arithmetic', 'leaf016': 'modern_arithmetic', 'leaf017': 'modern_arithmetic', 'leaf018': 'modern_arithmetic', 'leaf019': 'modern_arithmetic', 'leaf020': 'modern_arithmetic', 'leaf021': 'modern_arithmetic', 'leaf022': 'modern_arithmetic', 'leaf023': 'modern_arithmetic', 'leaf024': 'modern_arithmetic', 'leaf025': 'modern_arithmetic', 'leaf026': 'modern_arithmetic', 'leaf027': 'modern_arithmetic', 'leaf028': 'modern_arithmetic', 'leaf029': 'modern_arithmetic', 'leaf030': 'modern_arithmetic'}
PROBES=['check0','check1','check2','check3','check_all','cert_zero','specR','halts_iff']
PREFIX='SetTheory.BusyBeaver.ZFC.ControlBisimRotation240.'
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
    p.add_argument('--source',type=Path,default=HERE/'ControlBisimRotation240.lean')
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
    require([x['label']for x in b['parents']]==['leaf'+format(i,'03d')for i in range(31)],'Wrong exact ordered31 parents.')
    require([x['module']for x in b['parents']]==['BusyBeaver.ZFC.ControlBisimRotation240Chunk'+format(i,'03d')for i in range(31)],'Wrong31 leaf modules.')
    require(all(PARENT_CENSUS[x['label']][:2]==(1,1)for x in b['parents']),'Wrong leaf audit census.')
    generation=pin(b['generation']['path'],b['generation']['sha256']);g=json.loads(generation.read_text())
    require(g['status']=='GENERATED_SOURCE_ONLY_NO_PROOF_EXECUTION'and g['candidate_execution']is False and not g['fresh_objects'],'Wrong source-generation provenance.')
    require(len(g['units'])==30 and [x['index']for x in g['units']]==list(range(1,31)),'Wrong generated leaf inventory.')
    require(g['facade']['source']['sha256']==SOURCE_SHA and g['facade']['audit']['sha256']==AUDIT_SHA,'Wrong generated facade.')
    batchpath=pin(b['complete_batch']['path'],b['complete_batch']['sha256']);batch=json.loads(batchpath.read_text())
    require(batch['status']=='PASS_SELECTED_LEAF_RANGE'and batch['prepare_only']is False and batch['range']==dict(first=1,last=30),'Missing terminal complete remaining range.')
    require(batch['active_unit']is None and batch['before']==batch['after'],'Incomplete or changed final batch.')
    require(batch['generation']==b['generation']and batch['pilot']==b['parents'][0]['record']and batch['common']==b['common_record'],'Wrong complete-batch pedigree.')
    require(len(batch['completed_units'])==30 and [x['index']for x in batch['completed_units']]==list(range(1,31)),'Gaps/duplicates in actual leaf results.')
    require(len(batch['selected_units'])==30 and [x['index']for x in batch['selected_units']]==list(range(1,31)),'Wrong selected full range.')
    require(all(x['status']=='PASS'and x['record']==b['parents'][x['index']]['record']for x in batch['completed_units']),'Unbound or non-PASS actual leaf.')
    for generated,completed,selected in zip(g['units'],batch['completed_units'],batch['selected_units']):
        require(all(completed[k]==selected[k]==generated[k]for k in ('index','module','start','count','end')),'Changed actual interval/module.')
        spec=b['parents'][generated['index']]
        require(spec['source_sha256']==generated['source']['sha256']and spec['audit_sha256']==generated['audit']['sha256'],'Wrong actual generated source/audit binding.')
    require(g['units'][0]['start']==128 and g['units'][-1]['end']==3862 and all(x['end']-x['start']==x['count']and 0<x['count']<=128 for x in g['units'])and all(x['end']==y['start']for x,y in zip(g['units'],g['units'][1:])),'Changed complete interval partition.')
    pool={};externals={};toolpool={};parents={};evidence=[]
    for spec in b['parents']:
        label=spec['label'];E=pin(spec['record']['path'],PARENT_PINS[label]);e=json.loads(E.read_text());parents[label]=e;evidence.append(dict(path=str(E),sha256=PARENT_PINS[label]))
        require(label in PARENT_SCHEMAS and spec['schema']==PARENT_SCHEMAS[label],'Wrong explicit parent schema.')
        require(e['status']=='PASS'and e['prepare_only']is False and(e['named_axiom_probes'],e['callers'])==(spec['probes'],spec['callers'])==PARENT_CENSUS[label][:2],'Wrong actual parent.')
        require(spec['module']==e['fresh_modules'][0]['module'],'Wrong selected leaf identity.')
        if label!='leaf000':require(e['certificate_interval']=={k:g['units'][int(label[4:])-1][k]for k in ('index','group','start','count','end')}and e['generation']==b['generation'],'Wrong leaf interval/generation.')
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
    require(len(selected)==len(reused)==70 and external==set(b['direct_external_boundaries'])and external<=set(externals)and len(external)==3,'Wrong selected boundary.')
    require(providers==[q for q in parents['leaf000']['providers']if q['module']in external]and tools==parents['leaf000']['toolchain_providers'],'Changed external/tool selection.')
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
    require(imports(S)==[x['module']for x in b['parents']]and imports(A)==[MODULE],'Wrong source imports.')
    for m in imports(S):visit(m)
    require(seen==set(selected)==set(b['expected_projects'])and found==external and toolnames=={q['module']for q in tools},'Wrong exact import DFS.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==10,'Wrong8/10 audit.')
    for q in (S,A):require(not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text()),'Untrusted shortcut.')
    require(re.findall(r'^set_option .*$',S.read_text(),re.M)==['set_option autoImplicit false', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0']and not re.findall(r'^set_option .*$',A.read_text(),re.M),'Changed explicit source/audit option policy.')
    require(b['dependencies']==parents['leaf000']['dependencies'],'Wrong dependency metadata.');D=Path(b['dependencies']['root']);pin(D/'lake-manifest.json',b['dependencies']['lake_manifest_sha256'])
    def dependency_state():
        state={}
        for name in ('Foundation','Mathlib'):
            d=b['dependencies'][name];root=Path(d['path']);head=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip();dirty=subprocess.check_output(['git','-C',str(root),'status','--porcelain','--untracked-files=no'],text=True)
            require(head==d['pin']and d['tracked_clean']and not dirty,'Changed dependency '+name);state[name]=dict(pin=head,tracked_clean=True)
        return state
    dep_state=dependency_state();libs=[Path(x)for x in b['libraries']]
    require(b['libraries']==parents['leaf000']['LEAN_PATH'].split(os.pathsep)[1:]and all(x.is_dir()for x in libs),'Wrong existing library roots.')
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
    record=dict(status='PREPARED_NOT_BUILT'if args.prepare_only else'RUNNING',prepare_only=args.prepare_only,scope='Complete3862-entry certificate composition and arbitrary-IΣ1-model dag254/Rotation240 represented-interpreter halting equivalence; no final binary/validator/PA composition claim from this unit.',source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=evidence,parent_scope=b['scope'],compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,providers=providers,toolchain_providers=tools,actual_first_providers=actual,exact_project_prerequisite_count=70,exact_project_import_closure=sorted(seen),direct_external_boundaries=sorted(external),dependencies=b['dependencies'],before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],source_option_overrides=dict(maxRecDepth=100000,maxHeartbeats=0),audit_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
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
        post();record.update(status='PASS',named_axiom_probes=8,callers=10,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(c['output'].count('warning:')for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as post_error:record['postcheck_error']=repr(post_error)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
