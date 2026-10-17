"""Fresh-check all-internal raw-word nonemptiness and its exact audit.

Explicit successful raw-word evidence supplies all prerequisite project objects;
every current source/object is checked before and after use. Pinned cached
Foundation/Mathlib providers are identified, not rebuilt or independently
attested as a whole. No dependency build/fetch, all-internal proof execution,
or PA consistency transport is performed.
"""
from pathlib import Path
import argparse, importlib.util, json, os, re, shutil, subprocess, tempfile, time

SOURCE = Path('Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticProofWordNonempty254.lean')
AUDIT = Path('Computability/BusyBeaver/Research/ZFC/arithmetic_proof_word_nonempty254_audit.lean')
MODULE = 'BusyBeaver.ZFC.ArithmeticProofWordNonempty254'
PREFIX = 'SetTheory.BusyBeaver.ZFC.ArithmeticProofWordNonempty254.'
PROBES = ('consMp_ne_zero', 'consDrop_ne_zero', 'consAx_ne_zero', 'discard_ne_zero', 'leaf_ne_zero', 'bundle_ne_zero', 'gen_ne_zero', 'mp_ne_zero', 'rowValue_ne_zero', 'rawWord_succ_ne_zero', 'rawWord_eq_zero', 'compiledWord_eq_zero')
SOURCE_SHA256 = 'f577f11727654b7523024a8816293159859add3fbe1dae9d5cf1e73453f6970e'
AUDIT_SHA256 = '86ed678c0c3fbe057d54d91af0db680d619bfb8928cecb44430264418c46ba7b'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, required=True)
    p.add_argument('--word-evidence', type=Path, required=True)
    p.add_argument('--word-cache', type=Path, help='optional relocated overlay for all reused project objects')
    p.add_argument('--dependency-root', type=Path, required=True)
    p.add_argument('--library-path', type=Path, action='append', default=[])
    p.add_argument('--lean', type=Path)
    p.add_argument('--source', type=Path, help='explicit reviewed source override')
    p.add_argument('--audit', type=Path, help='explicit audit override; exact12/18 contract required')
    p.add_argument('--output', type=Path)
    p.add_argument('--prepare-only', action='store_true')
    a = p.parse_args()
    if not __debug__:
        p.error('Keep assertions enabled; do not use Python -O.')
    repo, root = a.repo.resolve(), a.dependency_root.resolve()
    helper = repo/'Computability/BusyBeaver/Research/ZFC/check_arithmetic_cantor.py'
    spec = importlib.util.spec_from_file_location('proof_nonempty_cantor_helpers', helper)
    if spec is None or spec.loader is None:
        p.error('Maintained Cantor helper is missing.')
    h = importlib.util.module_from_spec(spec); spec.loader.exec_module(h)
    dig = lambda q: h.digest(Path(q))
    source, audit = (a.source.resolve() if a.source else repo/SOURCE), (a.audit.resolve() if a.audit else repo/AUDIT)
    work = a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='zfc-proof-word-nonempty-check-'))
    h.fail(not any(work.is_relative_to(q) for q in (repo, root)), 'Use external scratch output.')
    h.fail(not work.exists() or not any(work.iterdir()), 'Use new/empty scratch output.')
    work.mkdir(parents=True, exist_ok=True)
    record = dict(status='PREPARING', scope=__doc__, commands=[], repo=str(repo), scratch=str(work), dependency_rebuild=False, downloads=False)
    def save():
        (work/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    try:
        h.fail(source.is_file() and audit.is_file(), 'Source/audit is missing.')
        h.fail(a.source is not None or dig(source)==SOURCE_SHA256, 'Maintained source changed; explicitly review/pass --source.')
        h.fail(a.audit is not None or dig(audit)==AUDIT_SHA256, 'Maintained audit changed; explicitly review/pass --audit.')
        h.fail(h.lean_imports(source.read_text())==['BusyBeaver.ZFC.ArithmeticProofWord254'], 'Unexpected adapter imports.')
        h.fail(h.lean_imports(audit.read_text())==[MODULE], 'Unexpected audit imports.')
        h.fail(re.findall(r'^#print axioms\s+(\S+)\s*$', audit.read_text(), re.M)==[PREFIX+n for n in PROBES], 'Expected exact ordered12-probe contract.')
        h.fail(len(re.findall(r'^example\b', audit.read_text(), re.M))==18, 'Expected18 stored callers.')
        ep = a.word_evidence.resolve(); base = json.loads(ep.read_text())
        h.fail(base.get('status')=='PASS' and base.get('named_axiom_probes')==28 and base.get('callers')==21 and base.get('only_standard_axioms') is True and base.get('all_input_provider_postchecks') is True, 'Need successful exact raw-word row/history evidence.')
        compiler, version = h.compiler_path(a.lean)
        h.fail(dig(compiler)==base['compiler']['sha256'] and version==base['compiler']['version'], 'Actual compiler differs from prior evidence.')
        libs, dependencies = h.dependency_libraries(root, a.library_path)
        for name in ('Foundation', 'Mathlib'):
            h.fail(dependencies[name]['pin']==base['dependencies'][name]['pin'], 'External dependency pin differs: '+name)
        h.fail(dependencies['lake_manifest_sha256']==base['dependencies']['lake_manifest_sha256'], 'Dependency manifest differs.')
        for name, row in dependencies['providers'].items():
            h.fail(row['sha256']==base['dependencies']['providers'][name]['sha256'], 'Actual first external provider differs: '+name)
        entries = list(base['chosen_modules'])
        for row in base['fresh_modules']:
            entries.append(dict(module=row['module'], source_sha256=row['source_sha256'], object=row['path'], object_sha256=row['sha256']))
        h.fail(len(entries)==27 and len({r['module'] for r in entries})==27, 'Expected27 distinct raw-word prerequisite modules.')
        reused=[]
        for row in entries:
            mod=row['module']
            h.fail(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+', mod) is not None, 'Unsafe module name.')
            if mod=='FirstOrder.Fol':
                rel=Path('Logic/FirstOrder/Lean/FirstOrder/Fol.lean')
            else:
                h.fail(mod.startswith('BusyBeaver.ZFC.'), 'Unexpected project module: '+mod)
                rel=Path('Computability/BusyBeaver/Lean')/Path(mod.replace('.', '/')).with_suffix('.lean')
            src=repo/rel
            # Explicit source overrides only affect the NEW adapter, not its prerequisites.
            obj=(a.word_cache.resolve()/Path(mod.replace('.', '/')).with_suffix('.olean')) if a.word_cache else Path(row['object'])
            h.fail(src.is_file() and obj.is_file() and dig(src)==row['source_sha256'] and dig(obj)==row['object_sha256'], 'Changed/missing reused module: '+mod)
            reused.append(dict(module=mod, source=str(src), source_sha256=dig(src), object=str(obj.resolve()), object_sha256=dig(obj)))
        required={q['module'] for q in reused}
        for row in reused:
            for imported in h.lean_imports(Path(row['source']).read_text()):
                h.fail(imported in required or imported.startswith(('Foundation.', 'Mathlib.')), 'Missing reused import: '+imported)
        providers=[]
        prior_providers=base.get('iteration_providers',base.get('providers',[]))
        for row in prior_providers:
            rel=Path(row['module'].replace('.', '/'))
            obj=next((q/rel.with_suffix('.olean') for q in libs if (q/rel.with_suffix('.olean')).is_file()), None)
            dep_name='Foundation' if row['module'].startswith('Foundation.') else 'Mathlib' if row['module'].startswith('Mathlib.') else None
            h.fail(dep_name is not None,'Unexpected external provider: '+row['module'])
            src=Path(dependencies[dep_name]['path'])/rel.with_suffix('.lean')
            h.fail(obj is not None and src.is_file() and dig(obj)==row['object_sha256'] and dig(src)==row['source_sha256'], 'Actual first iteration provider differs: '+row['module'])
            providers.append(dict(module=row['module'], source=str(src), source_sha256=dig(src), object=str(obj.resolve()), object_sha256=dig(obj), first_provider_in_actual_libraries=True))
        h.fail({'Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq'} <= {q['module'] for q in providers} <= {'Foundation.FirstOrder.Arithmetic.HFS.PRF','Foundation.FirstOrder.Arithmetic.HFS.Seq','Foundation.FirstOrder.Arithmetic.IOpen.Basic','Mathlib.Tactic.Ring'}, 'Incomplete/unexpected external providers.')
        cache=work/'cache'; cache.mkdir()
        for row in reused:
            dest=cache/Path(row['module'].replace('.', '/')).with_suffix('.olean'); dest.parent.mkdir(parents=True, exist_ok=True); dest.symlink_to(row['object'])
        snapshots=work/'sources'; local=snapshots/'BusyBeaver/ZFC'; local.mkdir(parents=True)
        compiled=[]
        for original in (source,):
            target=local/original.name; shutil.copyfile(original, target); compiled.append(target)
        aq=snapshots/'Audit.lean'; shutil.copyfile(audit, aq)
        inputs=[Path(__file__).resolve(), helper, compiler, ep, source, audit, *compiled, aq, root/'lake-manifest.json']
        for row in reused+providers:
            inputs.extend([Path(row['source']), Path(row['object'])])
        for row in dependencies['providers'].values():
            inputs.append(Path(row['path']))
        inputs=list(dict.fromkeys(q.resolve() for q in inputs)); before={str(q):dig(q) for q in inputs}
        env=dict(os.environ, LEAN_PATH=os.pathsep.join(map(str,[cache,*libs])), LEAN_NUM_THREADS='1')
        record.update(compiler=dict(path=str(compiler), version=version, sha256=dig(compiler)), source=dict(path=str(source), sha256=dig(source)), audit=dict(path=str(audit), sha256=dig(audit)), word_evidence=dict(path=str(ep), sha256=dig(ep)), reused_modules=reused, iteration_providers=providers, dependencies=dependencies, before=before, LEAN_PATH=env['LEAN_PATH'])
        if a.prepare_only:
            record['status']='PREPARED_NOT_BUILT'; save(); print(work/'verification.json'); return
        def run(label, q, obj=None):
            cmd=[str(compiler), '-M4096', '--root='+str(snapshots)]+(['-o',str(obj)] if obj else [])+[str(q)]
            t=time.monotonic(); r=subprocess.run(cmd, cwd=snapshots, env=env, text=True, capture_output=True); out=r.stdout+r.stderr
            log=work/(label+'.log'); log.write_text(out); record['commands'].append(dict(label=label, command=cmd, exit_code=r.returncode, seconds=time.monotonic()-t, log=str(log), output=out)); save()
            h.fail(r.returncode==0 and 'sorryAx' not in out and "declaration uses 'sorry'" not in out, 'Lean failed: '+str(log))
            print(label, 'PASS', round(time.monotonic()-t,3), flush=True); return out
        save(); fresh=[]
        for q in compiled:
            mod='BusyBeaver.ZFC.'+q.stem; obj=cache/Path(mod.replace('.', '/')).with_suffix('.olean')
            run(q.stem,q,obj); fresh.append(dict(module=mod,path=str(obj),sha256=dig(obj),source_sha256=dig(q)))
        out=run('audit',aq)
        reports=re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",out,re.S)
        h.fail([name for name,_ in reports]==[PREFIX+n for n in PROBES], 'Wrong ordered axiom reports.')
        h.fail(all(set(s.strip() for s in names.split(',') if s.strip())<={'propext','Classical.choice','Quot.sound'} for _,names in reports), 'Unexpected axioms.')
        after={str(q):dig(q) for q in inputs}; h.fail(before==after, 'Input/provider/compiler changed during check.')
        for row in reused:
            h.fail(dig(cache/Path(row['module'].replace('.', '/')).with_suffix('.olean'))==row['object_sha256'], 'Reused overlay changed.')
        for row in fresh:
            h.fail(dig(row['path'])==row['sha256'], 'Fresh object changed.')
        _, deps_after=h.dependency_libraries(root,a.library_path);h.fail(dependencies==deps_after,'Dependency identity/clean status changed.')
        record.update(status='PASS',after=after,all_input_provider_postchecks=True,fresh_modules=fresh,named_axiom_probes=12,callers=18,only_standard_axioms=True,axiom_reports=[dict(theorem=n,axioms=[s.strip() for s in names.split(',') if s.strip()]) for n,names in reports],warnings=sum(c['output'].count('warning:') for c in record['commands']))
    except Exception as e:
        record.update(status='FAIL',error=str(e)); save(); raise
    save(); print(work/'verification.json')

if __name__=='__main__': main()
