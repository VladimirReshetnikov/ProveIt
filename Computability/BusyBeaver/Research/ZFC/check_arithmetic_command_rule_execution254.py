"""Fresh-check exact internal GEN/MP numeric/Circuit contracts and11/8audit.

Explicit successful Leaf evidence supplies the exact36-project import closure.
Only the new Rule source and audit are built. Cached pinned external providers
are identified, not rebuilt or independently attested as a whole. No accepted
proof-code induction, scheduler, machine or PA endpoint is checked.
"""
from pathlib import Path
import argparse, importlib.util, json, os, re, shutil, subprocess, tempfile, time
MODULE='BusyBeaver.ZFC.ArithmeticCommandRuleExecution254'
SOURCE=Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCommandRuleExecution254.lean')
AUDIT=Path('Computability/BusyBeaver/Research/ZFC/arithmetic_command_rule_execution254_audit.lean')
SOURCE_SHA256='59dbbbe40ce3522f363eca602b2c0d7a9ad60802eeae39a4d5fbde2287a313c6'
AUDIT_SHA256='dab53eb75cf3f00f847d0e1bdfad0ceba751a090607ac5ba69d7c2aad0a58cb8'
PROBES=['SetTheory.'+MODULE+'.'+n for n in ('circuit_terminator','circuit_genBlock','circuit_mpBlock','gen_cleanup','eval_genTail','mp_cleanup','eval_mpTail','gen_contract','mp_contract','circuit_gen_contract','circuit_mp_contract')]
PROVIDERS={'Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring','Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True);p.add_argument('--leaf-evidence',type=Path,required=True)
    p.add_argument('--leaf-cache',type=Path,help='optional relocated overlay for all36 reused project modules')
    p.add_argument('--dependency-root',type=Path,required=True);p.add_argument('--library-path',type=Path,action='append',default=[])
    p.add_argument('--lean',type=Path);p.add_argument('--source',type=Path);p.add_argument('--audit',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--prepare-only',action='store_true');a=p.parse_args()
    if not __debug__:p.error('Python -O is unsupported; keep assertions enabled.')
    repo,root=a.repo.resolve(),a.dependency_root.resolve();helper=repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
    spec=importlib.util.spec_from_file_location('command_rule_cantor_helpers',helper)
    if spec is None or spec.loader is None:p.error('Maintained Cantor helper missing.')
    h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h);dig=lambda q:h.digest(Path(q))
    work=a.output.resolve()if a.output else Path(tempfile.mkdtemp(prefix='zfc-command-rule-check-'))
    h.fail(not any(work.is_relative_to(q)for q in (repo,root)),'Use external scratch output.')
    h.fail(not work.exists()or(work.is_dir()and not any(work.iterdir())),'Output must be new or empty.');work.mkdir(parents=True,exist_ok=True)
    record=dict(status='PREPARING',scope=__doc__,commands=[],repo=str(repo),scratch=str(work),dependency_rebuild=False,downloads=False,prepare_only=a.prepare_only)
    def save():(work/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    try:
        source=a.source.resolve()if a.source else repo/SOURCE;audit=a.audit.resolve()if a.audit else repo/AUDIT
        h.fail(source.is_file()and audit.is_file(),'Source/audit missing.')
        h.fail(a.source is not None or dig(source)==SOURCE_SHA256,'Maintained source changed; explicitly review/pass --source.')
        h.fail(a.audit is not None or dig(audit)==AUDIT_SHA256,'Maintained audit changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(source.read_text())==['BusyBeaver.ZFC.ArithmeticCommandLeafExecution254'],'Unexpected source imports.')
        h.fail(h.lean_imports(audit.read_text())==[MODULE],'Unexpected audit imports.')
        h.fail(re.findall(r'^#print axioms\s+(\S+)\s*$',audit.read_text(),re.M)==PROBES,'Expected exact ordered11 probes.')
        h.fail(len(re.findall(r'^example\b',audit.read_text(),re.M))==8,'Expected8 stored callers.')
        ep=a.leaf_evidence.resolve();e=json.loads(ep.read_text())
        h.fail(e.get('status')=='PASS'and e.get('named_axiom_probes')==12 and e.get('callers')==12 and e.get('only_standard_axioms')is True and e.get('all_input_provider_postchecks')is True,'Need successful exact Leaf12/12 evidence.')
        compiler,version=h.compiler_path(a.lean);h.fail(dig(compiler)==e['compiler']['sha256']and version==e['compiler']['version'],'Compiler differs from Leaf evidence.')
        libs,dependencies=h.dependency_libraries(root,a.library_path)
        for n in ('Foundation','Mathlib'):h.fail(dependencies[n]['pin']==e['dependencies'][n]['pin'],'Dependency pin differs: '+n)
        h.fail(dependencies['lake_manifest_sha256']==e['dependencies']['lake_manifest_sha256'],'Dependency manifest differs.')
        for m,q in dependencies['providers'].items():h.fail(q['sha256']==e['dependencies']['providers'][m]['sha256'],'Actual first base provider differs: '+m)
        entries=list(e['reused_modules']);q=e['module_object'];s=e['source']
        entries.append(dict(module='BusyBeaver.ZFC.ArithmeticCommandLeafExecution254',source_sha256=s['sha256'],object=q['path'],object_sha256=q['sha256']))
        h.fail(len(entries)==36 and len({q['module']for q in entries})==36,'Expected36 distinct Leaf prerequisites.')
        reused=[]
        for q in entries:
            m=q['module'];h.fail(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+',m)is not None,'Unsafe module name.')
            if m=='FirstOrder.Fol':src=repo/'Logic/FirstOrder/Lean/FirstOrder/Fol.lean'
            else:
                h.fail(m.startswith('BusyBeaver.ZFC.'),'Unexpected project module: '+m)
                src=repo/'Computability/BusyBeaver/Lean'/Path(m.replace('.','/')).with_suffix('.lean')
            obj=a.leaf_cache.resolve()/Path(m.replace('.','/')).with_suffix('.olean')if a.leaf_cache else Path(q['object'])
            h.fail(src.is_file()and obj.is_file()and dig(src)==q['source_sha256']and dig(obj)==q['object_sha256'],'Changed reused source/object: '+m)
            reused.append(dict(module=m,source=str(src),source_sha256=dig(src),object=str(obj.resolve()),object_sha256=dig(obj)))
        available={q['module']for q in reused};visited=set()
        def visit(m):
            if m.startswith(('Foundation.','Mathlib.')):return
            if m in visited:return
            h.fail(m in available,'Missing reused import: '+m);visited.add(m)
            q=next(q for q in reused if q['module']==m)
            for dep in h.lean_imports(Path(q['source']).read_text()):visit(dep)
        visit('BusyBeaver.ZFC.ArithmeticCommandLeafExecution254');h.fail(visited==available,'Reused overlay differs from exact import closure.')
        previous=e['providers'];h.fail(isinstance(previous,list),'Expected identified Leaf provider list.')
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
        inherited=e.get('same_source_object_alternatives',[])
        record.update(compiler=dict(path=str(compiler),version=version,sha256=dig(compiler)),source=dict(path=str(source),sha256=dig(source),snapshot=str(snap)),audit=dict(path=str(audit),sha256=dig(audit),snapshot=str(aq)),leaf_evidence=dict(path=str(ep),sha256=dig(ep)),reused_modules=reused,reused_count=len(reused),inherited_unused_object_alternatives=inherited,inherited_unused_object_alternatives_scope='Prior Leaf provenance only: these alternatives are not selected into this overlay, not relocated, and not rechecked here. Only reused_modules/providers are verified selected providers.',providers=providers,dependencies=dependencies,before=before,LEAN_PATH=env['LEAN_PATH'],memory_limit_mib=4096,fresh_modules=[])
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
        postchecks();record.update(status='PASS',named_axiom_probes=11,callers=8,only_standard_axioms=True,axiom_reports=[dict(theorem=n,axioms=[v.strip()for v in names.split(',')if v.strip()])for n,names in reports],warnings=sum(q['output'].count('warning:')for q in record['commands']))
    except Exception as exc:
        record.update(status='FAIL',error=str(exc));save();raise
    save();print(work/'verification.json')
if __name__=='__main__':main()
