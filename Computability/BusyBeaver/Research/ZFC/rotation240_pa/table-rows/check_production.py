#!/usr/bin/env python3
"""Serial exact Rotation240 row proofs; one shared120s source/audit budget per unit."""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
PILOT_PATH='/tmp/zfc-w6-table-rows240-pilot-actual/run2/verification.json'
PILOT_SHA='a1386bb2c23d6eeb450b82b97ea1effb66b6db34a2cc9fb5e4a7677d8ccea0c4'
PILOT_MODULE='BusyBeaver.ZFC.TableRowsRotation240Pilot'
PILOT_SOURCE='22ed9f69ea3ca249b44e7cfae11842736bbd4dbcedbe4f5c848da92a8ffb36e3'
PILOT_AUDIT='1ce38a72660e2e9b8d771164733ae658510a5dacc472d07cd069b82d8a836912'
GENERATOR_SHA='d74267d663af88f3f86263697265cb693211fed38daf08eec6eb2d45628a6281'
MANIFEST_SHA='aafb12a56d7cc9c9fbf2472551fea68742edecd0186839aa494dcfd44ea00361'
STANDARD={'propext','Classical.choice','Quot.sound'}
NS='SetTheory.BusyBeaver.ZFC.TableRowsRotation240.'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
rel=lambda m,s='.olean':Path(m.replace('.','/')).with_suffix(s)
imports=lambda p:re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',Path(p).read_text(),re.M)
def require(x,msg):
    if not x:raise RuntimeError(msg)
def descriptor(p):return dict(path=str(Path(p).resolve()),sha256=sha(p))
def reports(s):
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",s,re.M)]
def pin(tracked,p,h):
    p=Path(p).resolve();require(p.is_file()and sha(p)==h,'Changed input '+str(p));require(str(p)not in tracked or tracked[str(p)]==h,'Conflicting input pin.');tracked[str(p)]=h;return p
def merge(tracked,other):
    for p,h in other.items():pin(tracked,p,h)
def fresh_pair(e):
    f,=e['fresh_modules'];return dict(module=f['module'],source=e['source']['path'],source_sha256=f['source_sha256'],object=f['path'],object_sha256=f['sha256'])
def first_in(module,roots):
    p=next((root/rel(module)for root in roots if(root/rel(module)).is_file()),None);require(p is not None,'Missing first provider '+module);return p.resolve()
def validate_record(ref,spec,compiler,tracked,manifest_sha=None,guard_sha=None):
    """Read actual evidence only; never invokes a proof or supplied helper."""
    E=pin(tracked,ref['path'],ref['sha256']);e=json.loads(E.read_text())
    require(e['status']=='PASS'and e['prepare_only']is False and e['warnings']==0,'Only zero-warning actual PASS may supply objects.')
    require((e['named_axiom_probes'],e['callers'])==(len(spec['probes']),spec['callers']),'Wrong parent probe/caller census.')
    require(e['before']==e['after']and all(e[k]for k in ('all_input_provider_postchecks','all_fresh_objects_unchanged_after_audit','only_standard_axioms','source_object_recorded_before_audit')),'Incomplete parent evidence.')
    require(e['compiler']==compiler and not e['compiler_version_query_performed']and not e['dependency_build']and not e['downloads'],'Wrong parent compiler/execution scope.')
    require((e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'],e['source_option_overrides'],e['audit_option_overrides'])==(120,4096,'1',[],{},[]),'Wrong parent proof/execution limits.')
    merge(tracked,e['before'])
    for role in ('source','audit'):
        require(e[role]['sha256']==spec[role]['sha256'],'Wrong parent '+role)
        for key in ('path','snapshot'):pin(tracked,e[role][key],e[role]['sha256'])
    f,=e['fresh_modules'];pin(tracked,f['path'],f['sha256'])
    require(f['module']==spec['module']and f['source_sha256']==spec['source']['sha256'],'Wrong fresh parent module/source.')
    require(e['source_pass_object']==dict(f,source_command_index=0)and e['fresh_first_provider_before_audit']=={k:f[k]for k in ('module','path','sha256')},'Wrong pre-audit fresh capture.')
    require([c['label']for c in e['commands']]==['source','audit'],'Wrong parent command order.')
    for c in e['commands']:
        expected=[compiler['path'],'-j1','-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if c['label']=='source'else[])+[e[c['label']]['snapshot']]
        require(c['command']==expected and c['exit_code']==0 and c['timed_out']is False and c.get('interrupted')is None,'Wrong parent command/result.')
        pin(tracked,c['log'],c['log_sha256']);require(Path(c['log']).read_text()==c['output']and not any(s in c['output']for s in ('error:','warning:','sorryAx')),'Parent raw output changed/diagnostic.')
    at=Path(e['audit']['snapshot']).read_text();rr=reports(e['commands'][1]['output'])
    require(re.findall(r'^#print axioms (\S+)$',at,re.M)==spec['probes']==[q['name']for q in rr]and rr==e['axiom_reports']and all(set(q['axioms'])<=STANDARD for q in rr),'Wrong parent reports.')
    require(len(re.findall(r'^example\b',at,re.M))==spec['callers'],'Wrong typed parent callers.')
    pairs=e['reused_modules']+e['providers']+e['toolchain_providers'];first={q['module']:q for q in e['actual_first_providers']}
    require(len(first)==len(e['actual_first_providers'])and set(first)=={q['module']for q in pairs},'Parent provider census.')
    roots=[Path(x)for x in e['LEAN_PATH'].split(os.pathsep)]+[Path(compiler['path']).parent.parent/'lib/lean']
    for q in pairs:
        for k in ('source','object'):
            if k in q:p=pin(tracked,q[k],q[k+'_sha256']);require(e['before'].get(str(p))==q[k+'_sha256'],'Unbound parent provider.')
        actual=first_in(q['module'],roots);require(actual==Path(q['object']).resolve()==Path(first[q['module']]['actual_first']).resolve()and first[q['module']]['sha256']==q['object_sha256'],'Wrong current/historical first provider.')
    require(first_in(f['module'],roots)==Path(f['path']).resolve(),'Parent fresh object no longer first.')
    if manifest_sha is not None:
        require(e['manifest']['sha256']==manifest_sha and e['guard']['sha256']==guard_sha,'Different production manifest/guard.')
        prep=e['preparation'];pin(tracked,prep['path'],prep['sha256']);p=json.loads(Path(prep['path']).read_text())
        require(p['status']=='PREPARED_NOT_BUILT'and p['prepare_only']and p['commands']==[]and p['fresh_modules']==[]and p['before']==p['after']==e['before']and p['all_input_provider_postchecks'],'Invalid pre-proof preparation.')
    return e
def dependency_state(deps):
    state={}
    for name in ('Foundation','Mathlib'):
        d=deps[name];root=Path(d['path']);head=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip();dirty=subprocess.check_output(['git','-C',str(root),'status','--porcelain','--untracked-files=no'],text=True)
        require(head==d['pin']and d['tracked_clean']and not dirty,'Changed dependency '+name);state[name]=dict(pin=head,tracked_clean=True)
    return state
def check_manifest(m,tracked,pilot):
    require(GENERATOR_SHA is not None and m['generator']['sha256']==GENERATOR_SHA,'Unfrozen/changed emitter.')
    for d in (m['generator'],m['partition'],m['sites']):pin(tracked,d['path'],d['sha256'])
    require((m['cuts_per_module'],m['joins_per_module'],m['generated_units'],m['leaves'],m['guard_cases'],m['cuts'],m['joins'],m['fresh_row_checks'],m['generated_probes'],m['generated_callers'])==(32,32,35,6455,8386,530,529,529,1061,1061),'Wrong fixed production census/grouping.')
    require(m['reused_cut']==508 and m['pilot']['sha256']==PILOT_SHA and Path(m['pilot']['path']).resolve()==Path(PILOT_PATH).resolve(),'Wrong pilot reuse.')
    require(m['pilot']['fresh']==pilot['fresh_modules'][0]and m['pilot']['source']==pilot['source']and m['pilot']['audit']==pilot['audit'],'Wrong pilot descriptor.')
    require(m['root']==['join',528]and m['final_unit']==34 and m['final_module']=='BusyBeaver.ZFC.TableRowsRotation240','Wrong final unit.')
    require(m['compiler_or_checker_executed']is False and m['options']==dict(autoImplicit=False,new_proof_limit_overrides=[]),'Changed generation scope/options.')
    units=m['units'];require(len(units)==35 and len({u['module']for u in units})==35,'Unit identity census.')
    cut_items=[];join_items=[];reuses=[]
    for i,u in enumerate(units):
        require(u['index']==i and len(u['probes'])==u['callers']and len(set(u['probes']))==len(u['probes']),'Unit census.')
        require(u['dependencies']==sorted(set(u['dependencies']))and all(0<=x<i for x in u['dependencies']),'Non-acyclic dependencies.')
        require(u['parent_modules']==[units[x]['module']for x in u['dependencies']],'Dependency module binding.')
        expected=['BusyBeaver.ZFC.CountedTreeRotation240','BusyBeaver.ZFC.ControlTableBinding','BusyBeaver.ZFC.BisimCertRotation240']+u['parent_modules']+([PILOT_MODULE]if u['reused_cut']==508 else[])
        require(u['imports']==list(dict.fromkeys(expected)),'Exact declared imports.')
        S=pin(tracked,u['source']['path'],u['source']['sha256']);A=pin(tracked,u['audit']['path'],u['audit']['sha256'])
        require(imports(S)==u['imports']and imports(A)==[u['module']],'Source/audit imports.')
        require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==u['probes']and len(re.findall(r'^example\b',A.read_text(),re.M))==u['callers'],'Exact audit ABI.')
        for p in (S,A):require(re.findall(r'^set_option .*$',p.read_text(),re.M)==['set_option autoImplicit false']and not re.search(r'\b(sorry|admit|native_decide)\b',p.read_text()),'Changed proof options/shortcut.')
        if u['kind']=='cut':
            require(i<17 and u['dependencies']==[]and u['probes']==[NS+'block_'+str(n)for n in u['items']],'Cut unit layout.');cut_items+=u['items']
        elif u['kind']=='join':
            require(17<=i<34 and u['probes']==[NS+'join_'+str(n)for n in u['items']],'Join unit layout.');join_items+=u['items']
        else:require(i==34 and u['kind']=='final'and u['items']==[]and u['probes']==[NS+'all_rows',NS+'table_eq'],'Final theorem ABI.')
        if u['reused_cut']is not None:require(u['reused_cut']==508 and 508 in u['items'],'Pilot alias ownership.');reuses.append(i)
    require(cut_items==list(range(530))and join_items==list(range(529))and reuses==[15]and sum(len(u['probes'])for u in units)==1061,'Complete cut/join/probe coverage.')
def run_unit(u,m,manifest,guard,pilot,base_tracked,available,W,prepare_only):
    require(not W.exists(),'Fresh unit output required.');tracked={};merge(tracked,base_tracked)
    C=Path(pilot['compiler']['path']);S=pin(tracked,u['source']['path'],u['source']['sha256']);A=pin(tracked,u['audit']['path'],u['audit']['sha256'])
    pool={q['module']:q for q in pilot['reused_modules']};evidence=[dict(path=PILOT_PATH,sha256=PILOT_SHA)];parent_rows=[]
    if u['reused_cut']==508:pool[PILOT_MODULE]=fresh_pair(pilot)
    for i in u['dependencies']:
        require(i in available,'Missing actual prerequisite unit '+str(i));spec=m['units'][i];ref=available[i]
        e=validate_record(ref,spec,pilot['compiler'],tracked,manifest['sha256'],guard['sha256']);evidence.append(ref);parent_rows.append(dict(index=i,record=ref))
        for q in e['reused_modules']+[fresh_pair(e)]:
            if q['module']in pool:require(all(pool[q['module']][k]==q[k]for k in ('source_sha256','object_sha256','object')),'Conflicting parent pair.')
            else:pool[q['module']]=q
    ext={q['module']for q in pilot['providers']};tools={q['module']for q in pilot['toolchain_providers']};seen=set();found=set();used={'Init'}
    def visit(mod):
        if mod in tools:used.add(mod);return
        if mod in ext:found.add(mod);return
        require(mod in pool,'Import absent from actual parents '+mod)
        if mod in seen:return
        seen.add(mod)
        for child in imports(pool[mod]['source']):visit(child)
    for mod in u['imports']:visit(mod)
    require(found==ext and used==tools,'Wrong external/tool DFS.')
    allowed=set(q['module']for q in pilot['reused_modules'])|{PILOT_MODULE}|{m['units'][i]['module']for i in range(u['index'])}
    require(seen<=allowed and set(q['module']for q in pilot['reused_modules'])<=seen,'Wrong exact base/ancestor closure.')
    reused=[pool[mod]for mod in sorted(seen)];providers=pilot['providers'];toolpairs=pilot['toolchain_providers']
    for q in reused+providers+toolpairs:
        for k in ('source','object'):
            if k in q:pin(tracked,q[k],q[k+'_sha256'])
    deps=pilot['dependencies'];pin(tracked,Path(deps['root'])/'lake-manifest.json',deps['lake_manifest_sha256']);dep_state=dependency_state(deps)
    libs=[Path(x)for x in pilot['LEAN_PATH'].split(os.pathsep)[1:]];W.mkdir(parents=True);cache=W/'cache';cache.mkdir();snaps=W/'sources';snaps.mkdir()
    for q in reused:
        dest=cache/rel(q['module']);dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(Path(q['object']).resolve())
    ss=snaps/rel(u['module'],'.lean');ss.parent.mkdir(parents=True);shutil.copyfile(S,ss);aa=snaps/'Audit.lean';shutil.copyfile(A,aa);pin(tracked,ss,u['source']['sha256']);pin(tracked,aa,u['audit']['sha256'])
    roots=[cache,*libs,C.parent.parent/'lib/lean']
    def first(mod):return first_in(mod,roots)
    def provider_check():
        rows=[]
        for q in reused+providers+toolpairs:
            actual=first(q['module']);require(actual==Path(q['object']).resolve()and sha(actual)==q['object_sha256'],'Wrong first provider.');rows.append(dict(module=q['module'],actual_first=str(actual),sha256=sha(actual)))
        return rows
    actual=provider_check();env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
    r=dict(status='PREPARED_NOT_BUILT',prepare_only=True,unit_index=u['index'],module=u['module'],scope=m['scope'],source=dict(path=str(S),sha256=u['source']['sha256'],snapshot=str(ss)),audit=dict(path=str(A),sha256=u['audit']['sha256'],snapshot=str(aa)),manifest=manifest,guard=guard,provider_evidence=evidence,actual_generated_parents=parent_rows,compiler=pilot['compiler'],compiler_version_query_performed=False,reused_modules=reused,providers=providers,toolchain_providers=toolpairs,actual_first_providers=actual,exact_project_import_closure=sorted(seen),exact_project_prerequisite_count=len(reused),direct_external_boundaries=sorted(ext),dependencies=deps,before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],source_option_overrides={},audit_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
    def save():(W/'verification.json').write_text(json.dumps(r,indent=2)+'\n')
    def post():
        r['after']={p:sha(p)for p in tracked};require(r['after']==r['before']and provider_check()==actual and dependency_state(deps)==dep_state,'Input/provider postcheck failed.')
        for f in r['fresh_modules']:require(first(f['module'])==Path(f['path']).resolve()and sha(f['path'])==f['sha256'],'Fresh object changed.')
        r['all_input_provider_postchecks']=True
    save()
    try:
        post();save();prep=W/'preparation.json';prep.write_text(json.dumps(r,indent=2)+'\n')
        if prepare_only:return descriptor(W/'verification.json')
        r.update(status='RUNNING',prepare_only=False,preparation=descriptor(prep));save();deadline=time.monotonic()+120
        def run(label,file,obj=None):
            remaining=deadline-time.monotonic();require(remaining>0,'Shared deadline exhausted.')
            cmd=[str(C),'-j1','-M4096','--root='+str(snaps)]+(['-o',str(obj)]if obj else[])+[str(file)]
            started=time.monotonic();proc=subprocess.Popen(cmd,cwd=snaps,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True);timed_out=False;interrupted=None
            try:data,_=proc.communicate(timeout=remaining)
            except BaseException as ex:
                timed_out=isinstance(ex,subprocess.TimeoutExpired);interrupted=None if timed_out else type(ex).__name__
                try:os.killpg(proc.pid,signal.SIGKILL)
                except ProcessLookupError:pass
                data,_=proc.communicate()
            out=data.decode(errors='replace');log=W/(label+'.log');log.write_text(out);r['commands'].append(dict(label=label,command=cmd,seconds=time.monotonic()-started,exit_code=proc.returncode,timed_out=timed_out,interrupted=interrupted,output=out,log=str(log),log_sha256=sha(log)));save()
            require(not timed_out and interrupted is None and proc.returncode==0,label+' failed; exact log retained.');require('sorryAx'not in out and "declaration uses 'sorry'"not in out,'Untrusted output.');return out
        obj=cache/rel(u['module']);require(not obj.exists(),'Fresh target exists.');obj.parent.mkdir(parents=True,exist_ok=True);run('source',ss,obj)
        f=dict(module=u['module'],path=str(obj),sha256=sha(obj),source_sha256=u['source']['sha256']);r.update(fresh_modules=[f],source_pass_object=dict(f,source_command_index=0),source_object_recorded_before_audit=True,fresh_first_provider_before_audit=dict(module=u['module'],path=str(first(u['module'])),sha256=sha(first(u['module']))));require(first(u['module'])==obj.resolve(),'Fresh object not first.');save()
        out=run('audit',aa);rr=reports(out);require([x['name']for x in rr]==u['probes']and all(set(x['axioms'])<=STANDARD for x in rr),'Wrong ordered axiom reports.');require(not any('warning:'in c['output']for c in r['commands']),'Warning-bearing proof not accepted.')
        post();require(sha(prep)==r['preparation']['sha256'],'Preparation changed.');r.update(status='PASS',named_axiom_probes=len(u['probes']),callers=u['callers'],axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=0)
    except BaseException as ex:
        r.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as post_error:r['postcheck_error']=repr(post_error)
        save();raise
    save();return descriptor(W/'verification.json')
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--manifest',type=Path,required=True);p.add_argument('--manifest-sha',required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--start',type=int,default=0);p.add_argument('--count',type=int,default=35);p.add_argument('--prior-batch',nargs=2,action='append',default=[],metavar=('PATH','SHA256'));p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
    require(__debug__ and a.manifest_sha==MANIFEST_SHA,'No optimized Python; exact manifest SHA required.');W=a.output.resolve();require(not W.exists()and all(not W.is_relative_to(Path(q))for q in ('/home/codex/.codex/worktrees/ec20/Proofs','/home/codex/src/Proofs')),'Fresh external output only.')
    tracked={};M=pin(tracked,a.manifest,a.manifest_sha);guard=descriptor(__file__);pin(tracked,__file__,guard['sha256']);m=json.loads(M.read_text());manifest=descriptor(M)
    require(sha(PILOT_PATH)==PILOT_SHA,'Changed pilot record.');raw=json.loads(Path(PILOT_PATH).read_text());spec=dict(module=PILOT_MODULE,source=dict(sha256=PILOT_SOURCE),audit=dict(sha256=PILOT_AUDIT),probes=['SetTheory.BusyBeaver.ZFC.TableRowsRotation240Pilot.checked'],callers=1)
    pilot=validate_record(dict(path=PILOT_PATH,sha256=PILOT_SHA),spec,raw['compiler'],tracked);require(len(pilot['before'])==720 and len(pilot['reused_modules'])==46 and len(pilot['providers'])==3 and len(pilot['toolchain_providers'])==2,'Wrong pilot boundary.')
    check_manifest(m,tracked,pilot);available={};priors=[]
    for path,h in a.prior_batch:
        P=pin(tracked,path,h);d=json.loads(P.read_text());require(d['manifest']==manifest and d['guard']==guard and not d['prepare_only']and d['status']in ('PASS_SELECTED_UNITS','PASS_COMPLETE_TABLE_ROWS','FAIL'),'Wrong prior batch.');priors.append(descriptor(P))
        for row in d['completed_units']:
            i=row['unit_index'];require(0<=i<35 and row['module']==m['units'][i]['module']and row['status']=='PASS','Wrong prior unit.');ref=row['record'];validate_record(ref,m['units'][i],pilot['compiler'],tracked,manifest['sha256'],guard['sha256'])
            require(i not in available or available[i]==ref,'Conflicting successful unit records.');available[i]=ref
    require(0<=a.start<35 and 0<a.count<=35-a.start,'Wrong selected range.');selected=list(range(a.start,a.start+a.count));require(all(i not in available for i in selected),'Reuse successful units; do not replay.')
    W.mkdir(parents=True);r=dict(status='RUNNING',prepare_only=a.prepare_only,manifest=manifest,guard=guard,pilot=dict(path=PILOT_PATH,sha256=PILOT_SHA),prior_batches=priors,selected_unit_indices=selected,completed_units=[],prepared_units=[],active_unit=None,failed_unit=None,serial=True,shared_timeout_seconds_per_unit=120,dependency_build=False,downloads=False,compiler_version_query_performed=False)
    def save():
        t=W/'batch.json.tmp';t.write_text(json.dumps(r,indent=2)+'\n');t.replace(W/'batch.json')
    save();i=None
    try:
        for i in selected:
            u=m['units'][i];require(all(j in available for j in u['dependencies']),'Missing successful predecessor before selected unit.');r['active_unit']=i;save()
            ref=run_unit(u,m,manifest,guard,pilot,tracked,available,W/f'unit{i:03}',a.prepare_only)
            if a.prepare_only:r['prepared_units'].append(dict(unit_index=i,module=u['module'],record=ref,status='PREPARED_NOT_BUILT'))
            else:available[i]=ref;r['completed_units'].append(dict(unit_index=i,module=u['module'],record=ref,status='PASS'))
            save()
        if a.prepare_only:r['status']='PREPARED_NOT_BUILT'
        elif set(available)==set(range(35)):
            r.update(status='PASS_COMPLETE_TABLE_ROWS',selected_records={str(i):available[i]for i in range(35)},generated_units=35,generated_probes=1061,generated_callers=1061,including_pilot_probes=1062,including_pilot_callers=1062,leaves=6455,branch_cases=8386,cuts=530,joins=529,final_record=available[34])
        else:r['status']='PASS_SELECTED_UNITS'
        r['active_unit']=None;save()
    except BaseException as ex:r.update(status='FAIL',error=repr(ex),failed_unit=i);save();raise
    print(W/'batch.json')
if __name__=='__main__':main()
