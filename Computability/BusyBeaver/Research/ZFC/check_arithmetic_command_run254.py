"""Fresh-check exact command-word tick, internal run/drain, and stored audit.

Requires explicit successful command-rest and Append evidence. Only the two
new sources and audit are built; project and Foundation/Mathlib objects are
source/object matched and reused. The external dependency cache is identified,
not rebuilt or independently attested as a whole. No native execution adapter,
append execution, compiler execution, scheduler or PA endpoint is checked.
"""
from pathlib import Path
import argparse, importlib.util, json, os, re, shutil, subprocess, tempfile, time

TICK='BusyBeaver.ZFC.ArithmeticCommandTick254'
RUN='BusyBeaver.ZFC.ArithmeticCommandRun254'
EXPECTED={TICK:'c27e2a4025fe8112b5a3d5cd3e789e3ec8937c35c99d551a53a40e273fe82720',RUN:'22f881d35cfa4e1fd668143dc34c1e5cd88f93cf5235070db6f8285bc144958e'}
AUDIT_SHA256='47d7833b3d966980d851d51b5eef12777e9d4f61c1aa3e07141f4c7c5196f90e'
PROBES=[TICK+'.'+n for n in ('live_defined','remaining_defined','working_defined','live_decode','next_defined','tick_defined','tick_live_succ','tick_stopped','tick_decreases')]+[RUN+'.'+n for n in ('run_defined','run_defined_delta','run_succ','run_stopped','run_add','drain_bound','drained','terminal_defined','eval_defined','eval_defined_delta','eval_zero_word','terminal_stopped','eval_eq_zero_iff','totalitySentence_true','isigma1_proves_totality','peano_proves_totality')]
PROBES=['SetTheory.'+q for q in PROBES]

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--step-word-evidence',type=Path,required=True)
    p.add_argument('--step-word-cache',type=Path)
    p.add_argument('--append-evidence',type=Path,required=True,help='checked PRF/Seq providers; no Append object is imported')
    p.add_argument('--dependency-root',type=Path,required=True)
    p.add_argument('--library-path',type=Path,action='append',default=[])
    p.add_argument('--lean',type=Path)
    p.add_argument('--tick-source',type=Path)
    p.add_argument('--run-source',type=Path)
    p.add_argument('--audit',type=Path)
    p.add_argument('--output',type=Path)
    p.add_argument('--prepare-only',action='store_true')
    a=p.parse_args()
    if not __debug__:p.error('Python -O is unsupported; keep assertions enabled.')
    repo,root=a.repo.resolve(),a.dependency_root.resolve()
    helper=repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
    spec=importlib.util.spec_from_file_location('command_run_cantor_helpers',helper)
    if spec is None or spec.loader is None:p.error('Maintained Cantor helper missing.')
    h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
    dig=lambda q:h.digest(Path(q))
    work=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-run-check-'))
    h.fail(not any(work.is_relative_to(q)for q in (repo,root)),'Use external scratch output.')
    h.fail(not work.exists() or (work.is_dir() and not any(work.iterdir())),'Output must be new or empty.')
    work.mkdir(parents=True,exist_ok=True)
    record=dict(status='PREPARING',scope=__doc__,repo=str(repo),scratch=str(work),commands=[],dependency_rebuild=False,downloads=False,prepare_only=a.prepare_only)
    def save():(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    try:
        originals={TICK:a.tick_source.resolve() if a.tick_source else repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandTick254.lean',RUN:a.run_source.resolve() if a.run_source else repo/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandRun254.lean'}
        audit=a.audit.resolve() if a.audit else repo/'Computability/BusyBeaver/Research/ZFC/arithmetic_command_run254_audit.lean'
        for m,q in originals.items():
            h.fail(q.is_file(),'Source missing: '+m)
            override=a.tick_source if m==TICK else a.run_source
            h.fail(override is not None or dig(q)==EXPECTED[m],'Maintained source changed; explicitly review/pass override: '+m)
        h.fail(audit.is_file(),'Audit missing.')
        h.fail(a.audit is not None or dig(audit)==AUDIT_SHA256,'Maintained audit changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(originals[TICK].read_text())==['BusyBeaver.ZFC.ArithmeticCommandStepWord254'],'Unexpected Tick imports.')
        h.fail(h.lean_imports(originals[RUN].read_text())==[TICK,'Foundation.FirstOrder.Arithmetic.HFS.PRF'],'Unexpected Run imports.')
        h.fail(h.lean_imports(audit.read_text())==[RUN],'Unexpected audit imports.')
        h.fail(re.findall(r'^#print axioms\s+(\S+)\s*$',audit.read_text(),re.M)==PROBES,'Expected exact ordered25 probes.')
        h.fail(len(re.findall(r'^example\b',audit.read_text(),re.M))==30,'Expected30 stored callers.')
        ep,ap=a.step_word_evidence.resolve(),a.append_evidence.resolve();e=json.loads(ep.read_text());ae=json.loads(ap.read_text())
        h.fail(e.get('status')=='PASS' and e.get('named_axiom_probes')==3 and e.get('callers')==4 and e.get('all_sources_objects_providers_unchanged') is True and e.get('only_standard_axioms') is True,'Need successful exact StepWord3/4 evidence.')
        h.fail(ae.get('status')=='PASS' and ae.get('named_axiom_probes')==24 and ae.get('callers')==30 and ae.get('all_input_provider_identities_unchanged_after_check') is True and ae.get('fresh_object_unchanged_after_check') is True,'Need successful exact Append24/30 evidence.')
        compiler,version=h.compiler_path(a.lean)
        for old in (e,ae):h.fail(dig(compiler)==old['compiler']['sha256'] and version==old['compiler']['version'],'Compiler differs from prerequisite.')
        libs,dependencies=h.dependency_libraries(root,a.library_path)
        for old in (e,ae):
            for dep in ('Foundation','Mathlib'):h.fail(dependencies[dep]['pin']==old['dependencies'][dep]['pin'],'Dependency pin differs: '+dep)
            h.fail(dependencies['lake_manifest_sha256']==old['dependencies']['lake_manifest_sha256'],'Dependency manifest differs.')
            for m,q in dependencies['providers'].items():h.fail(q['sha256']==old['dependencies']['providers'][m]['sha256'],'Actual first base provider differs: '+m)
        entries=list(e['reused_modules']);entries.append(dict(module='BusyBeaver.ZFC.ArithmeticCommandStepWord254',source_sha256=e['source']['sha256'],object=e['module_object']['path'],object_sha256=e['module_object']['sha256']))
        h.fail(len(entries)==20 and len({q['module']for q in entries})==20,'Expected20 distinct StepWord prerequisite modules.')
        reused=[]
        for q in entries:
            m=q['module'];h.fail(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+',m)is not None,'Unsafe module name.')
            if m=='FirstOrder.Fol':src=repo/'Logic/FirstOrder/Lean/FirstOrder/Fol.lean'
            else:
                h.fail(m.startswith('BusyBeaver.ZFC.'),'Unexpected project module: '+m)
                src=repo/'Computability/BusyBeaver/Lean'/Path(m.replace('.','/')).with_suffix('.lean')
            obj=(a.step_word_cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean'))if a.step_word_cache else Path(q['object'])
            h.fail(src.is_file()and obj.is_file()and dig(src)==q['source_sha256']and dig(obj)==q['object_sha256'],'Changed reused source/object: '+m)
            reused.append(dict(module=m,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj)))
        available={q['module']for q in reused};visited=set()
        def visit(m):
            if m.startswith(('Foundation.','Mathlib.')):return
            if m in visited:return
            h.fail(m in available,'Missing project import: '+m);visited.add(m)
            row=next(q for q in reused if q['module']==m)
            for dep in h.lean_imports(Path(row['source']).read_text()):visit(dep)
        visit('BusyBeaver.ZFC.ArithmeticCommandStepWord254');h.fail(visited==available,'Prerequisite overlay is not exact import closure.')
        providers=[]
        for m,q in ae['providers'].items():
            h.fail(m in {'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'},'Unexpected provider '+m)
            rel=Path(m.replace('.','/'));obj=next((lib/rel.with_suffix('.olean')for lib in libs if (lib/rel.with_suffix('.olean')).is_file()),None)
            dep='Foundation'if m.startswith('Foundation.')else'Mathlib';src=Path(dependencies[dep]['path'])/rel.with_suffix('.lean')
            h.fail(obj is not None and src.is_file()and dig(obj)==q['sha256'],'Actual first provider mismatch: '+m)
            if 'source_sha256'in q:h.fail(dig(src)==q['source_sha256'],'Provider source mismatch: '+m)
            providers.append(dict(module=m,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj),first_provider_in_actual_libraries=True))
        h.fail(len(providers)==4,'Need4 exact providers.')
        cache=work/'cache';cache.mkdir();snapshots=work/'sources';local=snapshots/'BusyBeaver/ZFC';local.mkdir(parents=True)
        for q in reused:
            dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
        sources=[]
        for m,q in originals.items():
            target=local/(m.split('.')[-1]+'.lean');shutil.copyfile(q,target);sources.append(dict(module=m,path=str(q),sha256=dig(q),snapshot=str(target)))
        aq=snapshots/'Audit.lean';shutil.copyfile(audit,aq)
        inputs=[Path(__file__).resolve(),helper,compiler,ep,ap,audit,aq,root/'lake-manifest.json']+[Path(q[k])for q in sources for k in ('path','snapshot')]+[Path(q[k])for q in reused+providers for k in ('source','object')]+[Path(q['path'])for q in dependencies['providers'].values()]
        inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):dig(q)for q in inputs}
        env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
        record.update(compiler=dict(path=str(compiler),version=version,sha256=dig(compiler)),sources=sources,audit=dict(path=str(audit),sha256=dig(audit),snapshot=str(aq)),prerequisites=[dict(path=str(q),sha256=dig(q))for q in (ep,ap)],reused_modules=reused,reused_count=len(reused),same_source_object_alternatives=e.get('same_source_object_alternatives',[]),providers=providers,dependencies=dependencies,before=before,LEAN_PATH=env['LEAN_PATH'],memory_limit_mib=4096,fresh_modules=[])
        def postchecks():
            after={str(q):dig(q)for q in inputs};h.fail(before==after,'Input/provider/compiler changed during check.')
            for q in reused:h.fail(dig(cache/Path(q['module'].replace('.','/')).with_suffix('.olean'))==q['object_sha256'],'Reused overlay changed.')
            for q in record['fresh_modules']:h.fail(dig(q['path'])==q['sha256'],'Fresh object changed after source.')
            _,after_deps=h.dependency_libraries(root,a.library_path);h.fail(dependencies==after_deps,'Dependency pins/clean/provider status changed.')
            record.update(after=after,all_input_provider_postchecks=True,all_reused_objects_match_evidence=True,all_fresh_objects_unchanged_after_audit=True)
        if a.prepare_only:
            postchecks();record['status']='PREPARED_NOT_BUILT';save();print(work/'verification.json');return
        def run(label,q,obj=None):
            cmd=[str(compiler),'-M4096','--root='+str(snapshots)]+(['-o',str(obj)]if obj else[])+[str(q)]
            t=time.monotonic();r=subprocess.run(cmd,cwd=snapshots,env=env,text=True,capture_output=True);out=r.stdout+r.stderr;log=work/(label+'.log');log.write_text(out)
            record['commands'].append(dict(label=label,command=cmd,exit_code=r.returncode,seconds=time.monotonic()-t,log=str(log),output=out));save()
            h.fail(r.returncode==0 and 'sorryAx'not in out and "declaration uses 'sorry'"not in out,'Lean failed: '+str(log));print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
        save()
        for q in sources:
            obj=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');run(q['module'].split('.')[-1],Path(q['snapshot']),obj)
            record['fresh_modules'].append(dict(module=q['module'],path=str(obj),sha256=dig(obj),source_sha256=q['sha256']));save()
        out=run('audit',aq);reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
        h.fail([n for n,_ in reports]==PROBES,'Missing/extra/incorrectly ordered probes.')
        h.fail(all(set(v.strip()for v in names.split(',')if v.strip())<={'propext','Classical.choice','Quot.sound'}for _,names in reports),'Unexpected axiom.')
        postchecks();record.update(status='PASS',named_axiom_probes=25,callers=30,only_standard_axioms=True,axiom_reports=[dict(theorem=n,axioms=[v.strip()for v in names.split(',')if v.strip()])for n,names in reports],warnings=sum(q['output'].count('warning:')for q in record['commands']))
    except Exception as exc:
        record.update(status='FAIL',error=str(exc));save();raise
    save();print(work/'verification.json')
if __name__=='__main__':main()
