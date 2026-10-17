"""Fresh-check all-Nat agreement with actual Enum254.cexec and its exact audit.

Only the new Nat adapter/audit are built. Requires successful frozen Tick/Run
source/object evidence in its original or portable PASS schema; prepare-only
records no proof build. Existing pinned external dependency caches are
identified, not rebuilt or independently attested as a whole. No nonstandard
list-execution theorem, compiler execution or PA endpoint is inferred.
"""
from pathlib import Path
import argparse, importlib.util, json, os, re, shutil, subprocess, tempfile, time
MODULE='BusyBeaver.ZFC.ArithmeticCommandRunNat254'
SOURCE=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandRunNat254.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_run_nat254_audit.lean')
SOURCE_SHA256='7b4eb914bb0b68e8a7034ea2008a35a4b2e7d39c95fc2999596f90d335e03eeb'
AUDIT_SHA256='0baf7d77e02b7fce6c5aeb37789e6e265a39a7074c9f0125f57489f434522c64'
RUN_SOURCES={'BusyBeaver.ZFC.ArithmeticCommandTick254':'c27e2a4025fe8112b5a3d5cd3e789e3ec8937c35c99d551a53a40e273fe82720','BusyBeaver.ZFC.ArithmeticCommandRun254':'22f881d35cfa4e1fd668143dc34c1e5cd88f93cf5235070db6f8285bc144958e'}
PROBES=['SetTheory.'+MODULE+'.'+n for n in ('tick_encode_cons','run_succ_first','run_length','length_le_encode','terminal_encode','eval_encode','terminal_word','eval_word','encodeW_decodeW','terminal_all_nat','eval_all_nat','evalDef_all_nat')]
PROVIDERS={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True);p.add_argument('--run-evidence',type=Path,required=True)
    p.add_argument('--run-cache',type=Path,help='optional relocated overlay for all22 reused project modules')
    p.add_argument('--dependency-root',type=Path,required=True);p.add_argument('--library-path',type=Path,action='append',default=[])
    p.add_argument('--lean',type=Path);p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
    if not __debug__:p.error('Python -O is unsupported; keep assertions enabled.')
    repo,root=a.repo.resolve(),a.dependency_root.resolve();helper=repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
    spec=importlib.util.spec_from_file_location('command_run_nat_cantor_helpers',helper)
    if spec is None or spec.loader is None:p.error('Maintained Cantor helper missing.')
    h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h);dig=lambda q:h.digest(Path(q))
    work=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-run-nat-check-'))
    h.fail(not any(work.is_relative_to(q)for q in (repo,root)),'Use external scratch output.')
    h.fail(not work.exists()or(work.is_dir()and not any(work.iterdir())),'Output must be new or empty.');work.mkdir(parents=True,exist_ok=True)
    record=dict(status='PREPARING',scope=__doc__,commands=[],repo=str(repo),scratch=str(work),dependency_rebuild=False,downloads=False,prepare_only=a.prepare_only)
    def save():(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    try:
        source=a.source.resolve()if a.source else repo/SOURCE;audit=a.audit.resolve()if a.audit else repo/AUDIT
        h.fail(source.is_file()and audit.is_file(),'Source/audit missing.')
        h.fail(a.source is not None or dig(source)==SOURCE_SHA256,'Maintained source changed; explicitly review/pass --source.')
        h.fail(a.audit is not None or dig(audit)==AUDIT_SHA256,'Maintained audit changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(source.read_text())==['BusyBeaver.ZFC.ArithmeticCommandRun254'],'Unexpected source imports.')
        h.fail(h.lean_imports(audit.read_text())==[MODULE],'Unexpected audit imports.')
        h.fail(re.findall(r'^#print axioms\s+(\S+)\s*$',audit.read_text(),re.M)==PROBES,'Expected exact ordered12 probes.')
        h.fail(len(re.findall(r'^example\b',audit.read_text(),re.M))==15,'Expected15 stored callers.')
        ep=a.run_evidence.resolve();e=json.loads(ep.read_text())
        h.fail(e.get('status')=='PASS'and e.get('named_axiom_probes')==25 and e.get('callers')==30 and e.get('only_standard_axioms')is True,'Need successful exact Tick/Run25/30 evidence.')
        h.fail(e.get('all_fresh_objects_unchanged_after_audit')is True,'Prior fresh object postchecks absent.')
        if 'sources'in e and 'source'not in e:
            schema='portable';sources=e['sources'];h.fail(e.get('all_input_provider_postchecks')is True and isinstance(e['providers'],list),'Portable Run PASS schema mismatch.')
        elif 'source'in e and 'sources'not in e:
            schema='original';sources=e['source'];h.fail(e.get('all_inputs_sources_objects_providers_unchanged')is True and isinstance(e['providers'],dict),'Original Run PASS schema mismatch.')
        else:raise ValueError('Unknown/ambiguous Run evidence schema.')
        h.fail(isinstance(sources,list)and len(sources)==2 and{q['module']:q['sha256']for q in sources}==RUN_SOURCES,'Need frozen exact Tick/Run sources.')
        compiler,version=h.compiler_path(a.lean);h.fail(dig(compiler)==e['compiler']['sha256']and version==e['compiler']['version'],'Compiler differs from Run evidence.')
        libs,dependencies=h.dependency_libraries(root,a.library_path)
        for n in ('Foundation','Mathlib'):h.fail(dependencies[n]['pin']==e['dependencies'][n]['pin'],'Dependency pin differs: '+n)
        h.fail(dependencies['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Dependency manifest differs.')
        for m,q in dependencies['providers'].items():h.fail(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Actual first base provider differs: '+m)
        entries=list(e['reused_modules']);fresh=e['fresh_modules'];h.fail(len(fresh)==2 and{q['module']:q['source_sha256']for q in fresh}==RUN_SOURCES,'Prior fresh source/object bindings differ.')
        for q in fresh:entries.append(dict(module=q['module'],source_sha256=q['source_sha256'],object=q['path'],object_sha256=q['sha256']))
        h.fail(len(entries)==22 and len({q['module']for q in entries})==22,'Expected22 distinct Run prerequisites.')
        reused=[]
        for q in entries:
            m=q['module'];h.fail(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+',m)is not None,'Unsafe module name.')
            if m=='FirstOrder.Fol':src=repo/'Logic/FirstOrder/Lean/FirstOrder/Fol.lean'
            else:
                h.fail(m.startswith('BusyBeaver.ZFC.'),'Unexpected project module: '+m)
                src=repo/'Computability/BusyBeaver/Lean'/Path(m.replace('.','/')).with_suffix('.lean')
            obj=a.run_cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean')if a.run_cache else Path(q['object'])
            h.fail(src.is_file()and obj.is_file()and dig(src)==q['source_sha256']and dig(obj)==q['object_sha256'],'Changed reused source/object: '+m)
            reused.append(dict(module=m,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj)))
        available={q['module']for q in reused};visited=set()
        def visit(m):
            if m.startswith(('Foundation.','Mathlib.')):return
            if m in visited:return
            h.fail(m in available,'Missing reused import: '+m);visited.add(m)
            q=next(q for q in reused if q['module']==m)
            for dep in h.lean_imports(Path(q['source']).read_text()):visit(dep)
        visit('BusyBeaver.ZFC.ArithmeticCommandRun254');h.fail(visited==available,'Reused overlay differs from exact import closure.')
        previous=e['providers']if schema=='portable'else[dict(module=m,object=q['path'],object_sha256=q['sha256'],**{k:v for k,v in q.items()if k in ('source','source_sha256')})for m,q in e['providers'].items()]
        h.fail(len(previous)==4 and{q['module']for q in previous}==PROVIDERS,'Expected4 exact external providers.')
        providers=[]
        for q in previous:
            m=q['module'];rel=Path(m.replace('.','/'));obj=next((lib/rel.with_suffix('.olean')for lib in libs if(lib/rel.with_suffix('.olean')).is_file()),None)
            src=Path(dependencies['Foundation'if m.startswith('Foundation.')else'Mathlib']['path'])/rel.with_suffix('.lean')
            h.fail(obj is not None and src.is_file()and dig(obj)==q['object_sha256'],'Actual first provider object differs: '+m)
            if 'source_sha256'in q:h.fail(dig(src)==q['source_sha256'],'Provider source differs: '+m)
            providers.append(dict(module=m,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj),first_provider_in_actual_libraries=True))
        cache=work/'cache';cache.mkdir();snapshots=work/'sources';local=snapshots/'BusyBeaver/ZFC';local.mkdir(parents=True)
        for q in reused:
            dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
        snap=local/source.name;shutil.copyfile(source,snap);aq=snapshots/'Audit.lean';shutil.copyfile(audit,aq)
        inputs=[Path(__file__).resolve(),helper,compiler,ep,source,audit,snap,aq,root/'lake-manifest.json']+[Path(q[k])for q in reused+providers for k in ('source','object')]+[Path(q['path'])for q in dependencies['providers'].values()]
        inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):dig(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
        record.update(compiler=dict(path=str(compiler),version=version,sha256=dig(compiler)),source=dict(path=str(source),sha256=dig(source),snapshot=str(snap)),audit=dict(path=str(audit),sha256=dig(audit),snapshot=str(aq)),run_evidence=dict(path=str(ep),sha256=dig(ep)),run_evidence_schema=schema,reused_modules=reused,reused_count=len(reused),same_source_object_alternatives=e.get('same_source_object_alternatives',[]),providers=providers,dependencies=dependencies,before=before,LEAN_PATH=env['LEAN_PATH'],memory_limit_mib=4096,fresh_modules=[])
        def postchecks():
            after={str(q):dig(q)for q in inputs};h.fail(before==after,'Input/provider/compiler changed during check.')
            for q in reused:h.fail(dig(cache/Path(q['module'].replace('.','/')).with_suffix('.olean'))==q['object_sha256'],'Reused overlay changed.')
            for q in record['fresh_modules']:h.fail(dig(q['path'])==q['sha256'],'Fresh object changed after source.')
            _,after_deps=h.dependency_libraries(root,a.library_path);h.fail(dependencies==after_deps,'Dependency pins/clean/provider identities changed.')
            record.update(after=after,all_input_provider_postchecks=True,all_reused_objects_match_evidence=True,all_fresh_objects_unchanged_after_audit=True)
        if a.prepare_only:
            postchecks();record['status']='PREPARED_NOT_BUILT';save();print(work/'verification.json');return
        def run(label,q,obj=None):
            cmd=[str(compiler),'-M4096','--root='+str(snapshots)]+(['-o',str(obj)]if obj else[])+[str(q)];t=time.monotonic();r=subprocess.run(cmd,cwd=snapshots,env=env,text=True,capture_output=True);out=r.stdout+r.stderr;log=work/(label+'.log');log.write_text(out)
            record['commands'].append(dict(label=label,command=cmd,exit_code=r.returncode,seconds=time.monotonic()-t,log=str(log),output=out));save()
            h.fail(r.returncode==0 and'sorryAx'not in out and"declaration uses 'sorry'"not in out,'Lean failed: '+str(log));print(label,'PASS',round(time.monotonic()-t,3),flush=True);return out
        save();obj=cache/Path(MODULE.replace('.','/')).with_suffix('.olean');run('source',snap,obj);record['fresh_modules']=[dict(module=MODULE,path=str(obj),sha256=dig(obj),source_sha256=dig(source))];save();out=run('audit',aq)
        reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
        h.fail([n for n,_ in reports]==PROBES,'Missing/extra/incorrectly ordered probes.')
        h.fail(all(set(v.strip()for v in names.split(',')if v.strip())<={'propext','Classical.choice','Quot.sound'}for _,names in reports),'Unexpected axiom.')
        postchecks();record.update(status='PASS',named_axiom_probes=12,callers=15,only_standard_axioms=True,axiom_reports=[dict(theorem=n,axioms=[v.strip()for v in names.split(',')if v.strip()])for n,names in reports],warnings=sum(q['output'].count('warning:')for q in record['commands']))
    except Exception as exc:
        record.update(status='FAIL',error=str(exc));save();raise
    save();print(work/'verification.json')
if __name__=='__main__':main()
