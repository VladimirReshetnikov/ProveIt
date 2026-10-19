#!/usr/bin/env python3
"""Rotation240 blank/control halting:6 probes/8 callers,797 projects,6 cache boundaries.
Shared120s, -j1 -M4096, default new proof limits; no rebuild/version query/download.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,shutil,signal,subprocess,time
HERE=Path('/tmp/zfc-arithmetic-blank-control-rotation240')
MODULE='BusyBeaver.ZFC.ArithmeticBlankControlRotation240'
SOURCE_SHA='8bedaead86f8d9f035bc6779fc6d58415436ddd2bd31b5562569a948f46f3424'
AUDIT_SHA='f61e403a64e2a523f586a371d3578b6cff1fe618634806d1118118426045a077'
BOUNDARY_SHA='bb0fc9dca95c23165ee3a088ddc0d86fce8aaf246c48251030d9355e6792d8f1'
PARENT_PINS={'boot': 'a3905c25ca76f088156853e1ced188443a20aa9fd2b83452e22335384efa7434', 'global': 'b7f3302dcbe8c5c252632643813f74710f5d2e0b904bd7d5a72ba24d61a2ad26', 'startup': '102a766d11d2b5e0f6f2ce616da318744f3d7548123043f0ed09884432b4dfd9'}
PARENT_CENSUS={'boot': (16, 18, 6608), 'global': (6, 8, 6610), 'startup': (12, 14, 312)}
PARENT_SCHEMAS={'boot': 'modern_arithmetic', 'global': 'modern_arithmetic', 'startup': 'modern_arithmetic_no_option_summaries'}
PARENT_PROJECTS={'boot': 777, 'global': 701, 'startup': 43}
PROBES=['physical_seed_code', 'control_iff_seed_halts', 'control_iff_blank_halts', 'blank_iff_control_halts', 'pairs_iff_blank_halts', 'blankSentence_iff_control_halts']
PREFIX='SetTheory.BusyBeaver.ZFC.ArithmeticBlankControlRotation240.'
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(x,msg):
    if not x:raise RuntimeError(msg)
def rel(m,suffix='.olean'):return Path(m.replace('.','/')).with_suffix(suffix)
def imports(p):
    text=Path(p).read_text();clean=[];i=depth=0
    while i<len(text):
        if text.startswith('/-',i):depth+=1;i+=2
        elif depth and text.startswith('-/',i):depth-=1;i+=2
        elif depth:i+=1
        elif text.startswith('--',i):
            j=text.find('\n',i);i=len(text)if j<0 else j
        else:clean.append(text[i]);i+=1
    require(depth==0,'Unclosed source comment.')
    return re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',''.join(clean),re.M)
def reports(text):
    rr=re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",text,re.M)
    return [dict(name=n,axioms=sorted({x.strip()for x in a.split(',')if x.strip()}))for n,a in rr]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,default=HERE/'ArithmeticBlankControlRotation240.lean')
    p.add_argument('--audit',type=Path,default=HERE/'Audit.lean');p.add_argument('--boundary',type=Path,default=Path(__file__).resolve().with_name('boundary.json'))
    p.add_argument('--output',type=Path,required=True);p.add_argument('--prepare-only',action='store_true');args=p.parse_args()
    require(__debug__,'No optimized Python.');require(not BOUNDARY_SHA.startswith('PENDING_'),'Freeze the actual three-parent boundary first.');S,A,B,W=args.source.resolve(),args.audit.resolve(),args.boundary.resolve(),args.output.resolve()
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
        require(spec['schema']==PARENT_SCHEMAS[label],'Wrong explicit parent schema.')
        require(e['status']=='PASS'and e['prepare_only']is False and(e['named_axiom_probes'],e['callers'])==(spec['probes'],spec['callers'])==PARENT_CENSUS[label][:2],'Wrong actual parent.')
        require(e['before']==e['after']and e['all_input_provider_postchecks']and e['all_fresh_objects_unchanged_after_audit']and e['only_standard_axioms'],'Incomplete parent.')
        require(len(e['before'])==spec['before_inputs']==PARENT_CENSUS[label][2],'Wrong parent input census.')
        for path,h in e['before'].items():pin(path,h)
        require(e['compiler']==b['compiler']and not e['compiler_version_query_performed']and not e['dependency_build']and not e['downloads'],'Different compiler/execution scope.')
        require(e['warnings']==0,'Changed parent warning scope.')
        require((e['shared_timeout_seconds'],e['memory_mebibytes'],e['LEAN_NUM_THREADS'],e['global_option_overrides'])==(120,4096,'1',[]),'Wrong modern policy.')
        require(sorted(e['exact_project_import_closure'])==sorted(q['module']for q in e['reused_modules']),'Wrong parent closure.')
        require(e['dependencies']==b['dependencies']and e['LEAN_PATH'].split(os.pathsep)[1:]==b['libraries']and e['exact_project_prerequisite_count']==spec['projects']==PARENT_PROJECTS[label],'Wrong arithmetic dependency boundary.')
        if label=='startup':require('source_option_overrides'not in e and'audit_option_overrides'not in e,'Unexpected historical Startup option summaries.')
        else:require(e['source_option_overrides']=={}and e['audit_option_overrides']==[],'Changed arithmetic option summaries.')
        for role in ('source','audit'):
            require(e[role]['sha256']==spec[role+'_sha256'],'Wrong parent source/audit.');pin(e[role]['path'],e[role]['sha256']);pin(e[role]['snapshot'],e[role]['sha256'])
        require(re.findall(r'^set_option .*$',Path(e['source']['snapshot']).read_text(),re.M)==spec['source_options']and re.findall(r'^set_option .*$',Path(e['audit']['snapshot']).read_text(),re.M)==spec['audit_options'],'Changed parent proof options.')
        f,=e['fresh_modules'];pin(f['path'],f['sha256'])
        require(f['module']==spec['module']and f['source_sha256']==e['source']['sha256']and f['sha256']==spec['fresh_object_sha256'],'Wrong parent fresh object.')
        require(e['source_object_recorded_before_audit']and e['source_pass_object']==dict(f,source_command_index=0),'Missing source-pass capture.')
        require(e['fresh_first_provider_before_audit']=={k:f[k]for k in ('module','path','sha256')},'Wrong pre-audit first capture.')
        require([c['label']for c in e['commands']]==['source','audit'],'Parent command order.')
        for c in e['commands']:
            require(c['exit_code']==0 and c['timed_out']is False and c.get('interrupted')is None,'Parent command failure/timeout/interruption.')
            expected=[str(C),'-j1','-M4096','--root='+str(Path(e['audit']['snapshot']).parent)]+(['-o',f['path']]if c['label']=='source'else[])+[e[c['label']]['snapshot']]
            require(c['command']==expected,'Wrong parent arguments.')
            log=pin(c['log'],c['log_sha256']);require(log.read_text()==c['output'],'Changed raw parent log.')
            require(not any(x in c['output']for x in ('error:','warning:','sorryAx')),'Unexpected parent diagnostic.')
        an=re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M);rr=reports(e['commands'][1]['output'])
        require(len(an)==spec['probes']and an==[x['name']for x in rr]and rr==e['axiom_reports']and all(set(x['axioms'])<=STANDARD for x in rr),'Wrong parent raw reports.')
        require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M))==spec['callers'],'Wrong parent callers.')
        ep=e.get('providers',[]);old_first={q['module']:q for q in e['actual_first_providers']};oldroots=[Path(q)for q in e['LEAN_PATH'].split(os.pathsep)]+[C.parent.parent/'lib/lean']
        expectedfirst={q['module']for q in e['reused_modules']+ep+e['toolchain_providers']}
        require(len(old_first)==len(e['actual_first_providers'])and set(old_first)==expectedfirst,'Wrong historical first census.')
        for q in e['reused_modules']+ep+e['toolchain_providers']:
            for k in ('source','object'):
                if k in q:pp=pin(q[k],q[k+'_sha256']);require(e['before'].get(str(pp))==q[k+'_sha256'],'Unbound historical provider.')
            first_old=next((root/rel(q['module'])).resolve()for root in oldroots if(root/rel(q['module'])).is_file())
            require(first_old==Path(q['object']).resolve(),'Changed parent first provider.')
            captured=old_first[q['module']];require(Path(captured['actual_first']).resolve()==first_old and captured['sha256']==q['object_sha256'],'Wrong historical first capture.')
        first_fresh=next((root/rel(f['module'])).resolve()for root in oldroots if(root/rel(f['module'])).is_file())
        require(first_fresh==Path(f['path']).resolve(),'Wrong current parent fresh first provider.')
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
    require(len(selected)==len(reused)==797 and external==set(externals)==set(b['direct_external_boundaries'])|set(b['retained_external_boundaries'])and len(external)==6,'Wrong selected boundary.')
    require(providers==[externals[m]for m in sorted(externals)]and tools==parents['boot']['toolchain_providers'],'Changed external/tool selection.')
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
    require(imports(S)==['BusyBeaver.ZFC.ArithmeticStartupFrameRotation240', 'BusyBeaver.ZFC.ArithmeticControlSimulationRotation240', 'BusyBeaver.ZFC.ArithmeticStartupRotation240']and imports(A)==[MODULE],'Wrong source imports.')
    for m in imports(S):visit(m)
    require(seen==set(selected)==set(b['expected_projects'])and found==set(b['direct_external_boundaries'])and external-found==set(b['retained_external_boundaries'])and toolnames=={q['module']for q in tools},'Wrong exact import DFS.')
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M)==[PREFIX+n for n in PROBES]and len(re.findall(r'^example\b',A.read_text(),re.M))==8,'Wrong6/8 audit.')
    for q in (S,A):require(not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text()),'Untrusted shortcut/options.')
    require(re.findall(r'^set_option .*$',S.read_text(),re.M)==['set_option autoImplicit false']and not re.findall(r'^set_option .*$',A.read_text(),re.M),'Changed new default proof limits.')
    require(b['dependencies']==parents['boot']['dependencies'],'Wrong dependency metadata.');D=Path(b['dependencies']['root']);pin(D/'lake-manifest.json',b['dependencies']['lake_manifest_sha256'])
    def dependency_state():
        state={}
        for name in ('Foundation','Mathlib'):
            d=b['dependencies'][name];root=Path(d['path']);head=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip();dirty=subprocess.check_output(['git','-C',str(root),'status','--porcelain','--untracked-files=no'],text=True)
            require(head==d['pin']and d['tracked_clean']and not dirty,'Changed dependency '+name);state[name]=dict(pin=head,tracked_clean=True)
        return state
    dep_state=dependency_state();libs=[Path(x)for x in b['libraries']]
    require(b['libraries']==parents['boot']['LEAN_PATH'].split(os.pathsep)[1:]and all(x.is_dir()for x in libs),'Wrong existing library roots.')
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
    record=dict(status='PREPARED_NOT_BUILT'if args.prepare_only else'RUNNING',prepare_only=args.prepare_only,scope='Exact Rotation240 packed-control seed halting iff binary blank halting in every ISigma1 model, with both times internal. Three actual parents Boot16/18 run3, Global6/8 and Startup12/14. Full physical seed and finite-prefix absorption retained. Existing blank sentence evaluation included; no L2 scheduler or consistency-sentence equivalence. Default new6/8 source/audit limits, shared120s/j1/M4096; no rebuild or proof replay.',source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),boundary=dict(path=str(B),sha256=BOUNDARY_SHA),provider_evidence=evidence,parent_scope=b['scope'],compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,providers=providers,toolchain_providers=tools,actual_first_providers=actual,exact_project_prerequisite_count=797,exact_project_import_closure=sorted(seen),direct_external_boundaries=sorted(found),retained_external_boundaries=sorted(external-found),dependencies=b['dependencies'],before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,shared_timeout_seconds=120,global_option_overrides=[],source_option_overrides={},audit_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
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
        post();record.update(status='PASS',named_axiom_probes=6,callers=8,axiom_reports=rr,only_standard_axioms=True,all_fresh_objects_unchanged_after_audit=True,warnings=sum(c['output'].count('warning:')for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL',error=repr(ex))
        try:post()
        except BaseException as post_error:record['postcheck_error']=repr(post_error)
        save();raise
    save();print(W/'verification.json')
if __name__=='__main__':main()
