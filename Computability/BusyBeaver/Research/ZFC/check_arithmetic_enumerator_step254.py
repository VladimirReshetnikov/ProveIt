"""Fresh-check the exact arithmetic scheduler step and its14/12audit.

Explicit successful Rule evidence supplies the exact21-project scheduler-step import closure.
Only the maintained EnumeratorStep source and audit are built. Cached pinned external providers
are identified, not rebuilt or independently attested as a whole. All internal IOpen configurations and the all-Nat enumStep adapter are covered.
No internal scheduler iteration or PA consistency endpoint is checked.
"""
from pathlib import Path
import argparse, importlib.util, json, os, re, shutil, subprocess, tempfile, time
MODULE='BusyBeaver.ZFC.ArithmeticEnumeratorStep254'
SOURCE=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticEnumeratorStep254.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_enumerator_step254_audit.lean')
SOURCE_SHA256='ba51f2d060bb3e160f51626b21536fe12267e95e3a3a8c71adb18407d5721275'
AUDIT_SHA256='76ed9c92cbd5493b3d92a186e0d9d2eba781bd39ff368631b1ac6a5ed8acbb67'
PROBES=['SetTheory.'+MODULE+'.'+n for n in ('live_decode', 'advance_defined', 'step_defined', 'step_defined_delta', 'step_zero', 'step_live', 'step_boundary', 'step_active', 'advance_nonzero', 'step_active_decreases', 'step_total', 'command_unpacked_nat', 'advance_execAt_nat', 'step_encode_nat')]
PROVIDERS={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True);p.add_argument('--rule-evidence',type=Path,required=True)
    p.add_argument('--rule-cache',type=Path,help='optional relocated overlay for all37 reused project modules')
    p.add_argument('--dependency-root',type=Path,required=True);p.add_argument('--library-path',type=Path,action='append',default=[])
    p.add_argument('--lean',type=Path);p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
    if not __debug__:p.error('Python -O is unsupported; keep assertions enabled.')
    repo,root=a.repo.resolve(),a.dependency_root.resolve();helper=repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
    spec=importlib.util.spec_from_file_location('proof_word_correct_cantor_helpers',helper)
    if spec is None or spec.loader is None:p.error('Maintained Cantor helper missing.')
    h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h);dig=lambda q:h.digest(Path(q))
    work=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-enumerator-step-check-'))
    h.fail(not any(work.is_relative_to(q)for q in (repo,root)),'Use external scratch output.')
    h.fail(not work.exists()or(work.is_dir()and not any(work.iterdir())),'Output must be new or empty.');work.mkdir(parents=True,exist_ok=True)
    record=dict(status='PREPARING',scope=__doc__,commands=[],repo=str(repo),scratch=str(work),dependency_rebuild=False,downloads=False,prepare_only=a.prepare_only)
    def save():(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    try:
        source=a.source.resolve()if a.source else repo/SOURCE;audit=a.audit.resolve()if a.audit else repo/AUDIT
        h.fail(source.is_file()and audit.is_file(),'Source/audit missing.')
        h.fail(a.source is not None or dig(source)==SOURCE_SHA256,'Maintained source changed; explicitly review/pass --source.')
        h.fail(a.audit is not None or dig(audit)==AUDIT_SHA256,'Maintained audit changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(source.read_text())==['BusyBeaver.ZFC.ArithmeticCommandTick254'],'Unexpected source imports.')
        h.fail(h.lean_imports(audit.read_text())==[MODULE],'Unexpected audit imports.')
        h.fail(re.findall(r'^#print axioms\s+(\S+)\s*$',audit.read_text(),re.M)==PROBES,'Expected exact ordered14 probes.')
        h.fail(len(re.findall(r'^example\b',audit.read_text(),re.M))==12,'Expected12 stored callers.')
        ep=a.rule_evidence.resolve();e=json.loads(ep.read_text())
        h.fail(e.get('status')=='PASS'and e.get('named_axiom_probes')==11 and e.get('callers')==8 and e.get('only_standard_axioms')is True and e.get('all_input_provider_postchecks')is True and e.get('all_fresh_objects_unchanged_after_audit')is True,'Need successful exact Rule11/8 evidence.')
        compiler,version=h.compiler_path(a.lean);h.fail(dig(compiler)==e['compiler']['sha256']and version==e['compiler']['version'],'Compiler differs from Rule evidence.')
        libs,dependencies=h.dependency_libraries(root,a.library_path)
        for n in ('Foundation','Mathlib'):h.fail(dependencies[n]['pin']==e['dependencies'][n]['pin'] and dependencies[n]['tracked_clean'] is True and e['dependencies'][n]['tracked_clean'] is True,'Dependency pin/clean differs: '+n)
        h.fail(dependencies['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Dependency manifest differs.')
        for m,q in dependencies['providers'].items():h.fail(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Actual first base provider differs: '+m)
        entries=list(e['reused_modules']);h.fail(len(e['fresh_modules'])==1,'Expected one fresh Rule object.')
        q=e['fresh_modules'][0];s=e['source']
        h.fail(q['module']=='BusyBeaver.ZFC.ArithmeticCommandRuleExecution254' and q['source_sha256']==s['sha256'],'Fresh Rule identity mismatch.')
        entries.append(dict(module=q['module'],source_sha256=s['sha256'],object=q['path'],object_sha256=q['sha256']))
        h.fail(len(entries)==37 and len({q['module']for q in entries})==37,'Expected37 distinct Rule prerequisites.')
        reused=[]
        for q in entries:
            m=q['module'];h.fail(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+',m)is not None,'Unsafe module name.')
            if m=='FirstOrder.Fol':src=repo/'Logic/FirstOrder/Lean/FirstOrder/Fol.lean'
            else:
                h.fail(m.startswith('BusyBeaver.ZFC.'),'Unexpected project module: '+m)
                src=repo/'Computability/BusyBeaver/Lean'/Path(m.replace('.','/')).with_suffix('.lean')
            obj=a.rule_cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean')if a.rule_cache else Path(q['object'])
            h.fail(src.is_file()and obj.is_file()and dig(src)==q['source_sha256']and dig(obj)==q['object_sha256'],'Changed reused source/object: '+m)
            reused.append(dict(module=m,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj)))
        available={q['module']for q in reused};visited=set();external=set()
        def visit(m):
            if m.startswith(('Foundation.','Mathlib.')):external.add(m);return
            if m in visited:return
            h.fail(m in available,'Missing reused import: '+m);visited.add(m)
            q=next(q for q in reused if q['module']==m)
            for dep in h.lean_imports(Path(q['source']).read_text()):visit(dep)
        visit('BusyBeaver.ZFC.ArithmeticCommandTick254');h.fail(len(visited)==21,'Expected21 exact prerequisite modules.');reused=[q for q in reused if q['module']in visited]
        previous=e['providers'];h.fail(isinstance(previous,list),'Expected identified Rule provider list.')
        h.fail(len(previous)==4 and{q['module']for q in previous}==PROVIDERS,'Expected4 exact external providers.')
        providers=[]
        for q in previous:
            m=q['module'];rel=Path(m.replace('.','/'));obj=next((lib/rel.with_suffix('.olean')for lib in libs if(lib/rel.with_suffix('.olean')).is_file()),None)
            src=Path(dependencies['Foundation'if m.startswith('Foundation.')else'Mathlib']['path'])/rel.with_suffix('.lean')
            h.fail(obj is not None and src.is_file()and dig(obj)==q['object_sha256'],'Actual first provider object differs: '+m)
            if 'source_sha256'in q:h.fail(dig(src)==q['source_sha256'],'Provider source differs: '+m)
            providers.append(dict(module=m,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj),first_provider_in_actual_libraries=True))
        direct_external_providers=[]
        for m in sorted(external):
            rel=Path(m.replace('.','/'));obj=next((lib/rel.with_suffix('.olean')for lib in libs if(lib/rel.with_suffix('.olean')).is_file()),None)
            src=Path(dependencies['Foundation'if m.startswith('Foundation.')else'Mathlib']['path'])/rel.with_suffix('.lean')
            h.fail(obj is not None and src.is_file(),'Missing direct external import: '+m)
            direct_external_providers.append(dict(module=m,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj),first_provider_in_actual_libraries=True))
        cache=work/'cache';cache.mkdir();snapshots=work/'sources';local=snapshots/'BusyBeaver/ZFC';local.mkdir(parents=True)
        for q in reused:
            dest=cache/Path(q['module'].replace('.','/')).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(q['object'])
        snap=local/source.name;shutil.copyfile(source,snap);aq=snapshots/'Audit.lean';shutil.copyfile(audit,aq)
        inputs=[Path(__file__).resolve(),helper,compiler,ep,source,audit,snap,aq,root/'lake-manifest.json']+[Path(q[k])for q in reused+providers+direct_external_providers for k in ('source','object')]+[Path(q['path'])for q in dependencies['providers'].values()]
        inputs=list(dict.fromkeys(q.resolve()for q in inputs));before={str(q):dig(q)for q in inputs};env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])),LEAN_NUM_THREADS='1')
        record.update(compiler=dict(path=str(compiler),version=version,sha256=dig(compiler)),source=dict(path=str(source),sha256=dig(source),snapshot=str(snap)),audit=dict(path=str(audit),sha256=dig(audit),snapshot=str(aq)),rule_evidence=dict(path=str(ep),sha256=dig(ep)),reused_modules=reused,reused_count=len(reused),inherited_unused_object_alternatives=e.get('same_source_object_alternatives',[]),inherited_unused_object_alternatives_scope='Prior evidence provenance only; unused alternatives are not selected, relocated or rechecked here.',providers=providers,direct_external_providers=direct_external_providers,actual_project_providers=[dict(module=q['module'],path=str(cache/Path(q['module'].replace('.','/')).with_suffix('.olean')),resolved=str(Path(q['object']).resolve()),sha256=q['object_sha256'],actual_first_provider=True)for q in reused],exact_project_import_closure=True,dependencies=dependencies,before=before,LEAN_PATH=env['LEAN_PATH'],memory_limit_mib=4096,fresh_modules=[])
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
        postchecks();record.update(status='PASS',named_axiom_probes=14,callers=12,only_standard_axioms=True,axiom_reports=[dict(theorem=n,axioms=[v.strip()for v in names.split(',')if v.strip()])for n,names in reports],warnings=sum(q['output'].count('warning:')for q in record['commands']))
    except Exception as exc:
        record.update(status='FAIL',error=str(exc));save();raise
    save();print(work/'verification.json')
if __name__=='__main__':main()
