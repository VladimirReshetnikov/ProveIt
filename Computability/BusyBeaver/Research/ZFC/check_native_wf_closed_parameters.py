#!/usr/bin/env python3
"""Closed native-WF syntax parameter Good: seven probes/ten typed callers.
Actual core+closed quotation and selected WellFoundedPart ancestors only.
Shared120s source/audit, -j1,-M4096; no proof limits/version/build/download.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time

HERE = Path(__file__).resolve().parent
MODULE = 'ZFCinPA.NativeWFClosedParameters'
SOURCE_SHA = '1979aa96a8de7adc2fcb24867fa2fe2c2aa8ddb61fed844de28bb0a0d53c16fc'
AUDIT_SHA = '2c061abb5343152786a86cf0605fa606bd70cc918e72572ad217a68c462dcb9c'
BOUNDARY_SHA = '1959f9b3fbcb17ebf705b0145aa50f8a0671f057879688bac555bd6fa661a5da'
PARENT_SHAS = {'core': '3a89f58fd858fe4662c37eb6be85f14685763f02f3cfdc951eecffc103670c8c', 'quotation': 'c7016a4f62755a98eee82bef7ed02c67877117d216510e840edd249850456aba', 'binary': '41ff9364f37d9eb33ff1eb2b4bbc0e5f17f0a44ac02a4a7dcdbdfa6c5b1ccf87'}
PROJECTS = set(['BoundedPAConsistency.InternalRelativization', 'BusyBeaver.ZFC.CompositionModel', 'BusyBeaver.ZFC.DeepPositiveClosure', 'BusyBeaver.ZFC.FiniteSets', 'BusyBeaver.ZFC.PositiveClosure', 'BusyBeaver.ZFC.PowerSyntax', 'BusyBeaver.ZFC.ProfileAxioms', 'BusyBeaver.ZFC.ProfileCollection', 'BusyBeaver.ZFC.ProfileComposition', 'BusyBeaver.ZFC.ProfileCongruence', 'BusyBeaver.ZFC.ProfileModel', 'BusyBeaver.ZFC.ProfilePairs', 'BusyBeaver.ZFC.ProfileSyntax', 'BusyBeaver.ZFC.QuotientBasic', 'BusyBeaver.ZFC.QuotientCPGIC', 'BusyBeaver.ZFC.QuotientModel', 'BusyBeaver.ZFC.QuotientPower', 'BusyBeaver.ZFC.QuotientSeparation', 'BusyBeaver.ZFC.SingletonInfinity', 'BusyBeaver.ZFC.WellFoundedPart', 'FirstOrder.Calculus', 'FirstOrder.Fol', 'ZF.Zf', 'ZFCinPA.Instances', 'ZFCinPA.InternalInterpretation', 'ZFCinPA.RawFormQuotation', 'ZFCinPA.SetRelativization'])
PROBES = ['isSemiformula_domainCode','isSemiformula_equalityCode','isSemiformula_membershipCode','shift_domainCode','shift_equalityCode','shift_membershipCode','good_parameter']
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def imports(p):
    return re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$', Path(p).read_text(), re.M)

def rel(m, suffix='.olean'):
    return Path(m.replace('.', '/')).with_suffix(suffix)

def reports(text):
    rows = re.findall(r"^'([^\n]+)'[ \t]+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", text, re.M)
    return [dict(name=n, axioms=sorted({x.strip() for x in a.split(',') if x.strip()})) for n, a in rows]

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo', type=Path, default=HERE.parents[3])
    p.add_argument('--dependency-root', type=Path, default=Path('/home/codex/src/Proofs'))
    p.add_argument('--source', type=Path, default=HERE.parents[3]/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeWFClosedParameters.lean')
    p.add_argument('--audit', type=Path, default=HERE/'native_wf_closed_parameters_audit.lean')
    p.add_argument('--boundary', type=Path, default=HERE/'results/native-wf-closed-parameters-boundary.json')
    p.add_argument('--core-evidence', type=Path)
    p.add_argument('--quotation-evidence', type=Path)
    p.add_argument('--binary-evidence', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--prepare-only', action='store_true')
    args = p.parse_args()
    require(__debug__, 'Python -O is unsupported.')
    R, D, W = args.repo.resolve(), args.dependency_root.resolve(), args.output.resolve()
    S, A, B = args.source.resolve(), args.audit.resolve(), args.boundary.resolve()
    require(not W.is_relative_to(R) and not W.is_relative_to(D), 'Output must be outside maintained/dependency roots.')
    require(not W.exists() or (W.is_dir() and not any(W.iterdir())), 'Fresh output required.')
    require(sha(S) == SOURCE_SHA and sha(A) == AUDIT_SHA and sha(B) == BOUNDARY_SHA, 'Changed source/audit/boundary.')
    b = json.loads(B.read_text()); tracked = {}
    def pin(path, expected):
        q = Path(path).resolve()
        require(q.is_file() and sha(q) == expected, 'Changed or absent input: ' + str(q))
        require(str(q) not in tracked or tracked[str(q)] == expected, 'Conflicting input identity: ' + str(q))
        tracked[str(q)] = expected
        return q
    for q in (Path(__file__).resolve(), S, A, B):
        pin(q, sha(q))
    evidence = {}; parent_summaries = {}; parent_snapshots = []; parent_rows = {}
    for key, override in [('core',args.core_evidence),('quotation',args.quotation_evidence),('binary',args.binary_evidence)]:
        desc = b['parents'][key]; E = pin(override or desc['path'], PARENT_SHAS[key])
        require(desc['sha256'] == PARENT_SHAS[key], 'Boundary parent pin mismatch.')
        e = json.loads(E.read_text()); evidence[key] = e
        expected_census = {'core':(7,13),'quotation':(5,8),'binary':(11,11)}[key]
        require(e['status'] == 'PASS' and (e['named_axiom_probes'],e['callers']) == expected_census, 'Wrong parent status/census.')
        require(e['before'] == e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'], 'Incomplete parent evidence.')
        require([q['label'] for q in e['commands']] == ['source','audit'] and all(q['exit_code'] == 0 and not q['timed_out'] for q in e['commands']), 'Wrong parent commands.')
        require(all(e['compiler'][k] == b['compiler'][k] for k in ('path','sha256','version')), 'Different parent compiler.')
        # Pin immutable actual snapshots. Do not apply old before hashes to superseded maintained files.
        for field in ['source','audit']:
            pin(e[field]['snapshot'],e[field]['sha256'])
        parent_snapshots.append(dict(parent=key,source=e['source'],audit=e['audit']))
        names = re.findall(r'^#print axioms (\S+)$',Path(e['audit']['snapshot']).read_text(),re.M)
        rr = reports(e['commands'][1]['output'])
        expanded_names = ['LeanProofs.ZFCinPA.'+n for n in names] if key == 'core' else names
        require([q['name'] for q in rr] == expanded_names and len(names) == expected_census[0] and all(set(q['axioms']) <= STANDARD for q in rr), 'Wrong parent raw axiom audit.')
        require(len(re.findall(r'^example\b',Path(e['audit']['snapshot']).read_text(),re.M)) == expected_census[1], 'Wrong parent typed callers.')
        rows = {q['module']:dict(q) for q in e['reused_modules']}
        require(len(rows) == len(e['reused_modules']), 'Duplicate parent modules.')
        if key in ('core','quotation'):
            require(len(e['fresh_modules']) == 1 and e['source_object_recorded_before_audit'], 'Missing selected fresh capture.')
            f = e['fresh_modules'][0]; captured=e['source_pass_object']; first_f=e['fresh_first_provider_before_audit']
            require(all(captured[k] == f[k] for k in ('module','path','sha256','source_sha256')) and captured['source_command_index'] == 0 and f['source_sha256'] == e['source']['sha256'], 'Fresh source binding mismatch.')
            first_path=first_f.get('path',first_f.get('resolved',first_f.get('actual_first')))
            require(first_f['module'] == f['module'] and Path(first_path).resolve() == Path(f['path']).resolve() and first_f['sha256'] == f['sha256'], 'Wrong pre-audit first provider.')
            pin(f['path'],f['sha256'])
            rows[f['module']]=dict(module=f['module'],source=e['source']['snapshot'],source_sha256=e['source']['sha256'],object=f['path'],object_sha256=f['sha256'],selected_fresh=True)
        parent_rows[key]=rows
        parent_summaries[key]=dict(path=str(E),sha256=PARENT_SHAS[key],named_axiom_probes=e['named_axiom_probes'],callers=e['callers'],warnings=e['warnings'],historical_reused_project_count=len(e['reused_modules']),all_ancestor_inputs_rehashed=False,scope=b['parent_scope'][key])
    core, quotation, binary = evidence['core'],evidence['quotation'],evidence['binary']
    require(re.findall(r'^#print axioms (\S+)$',A.read_text(),re.M) == ['LeanProofs.ZFCinPA.NativeWFClosedParameters.'+n for n in PROBES], 'Wrong ordered audit probes.')
    require(len(re.findall(r'^example\b',A.read_text(),re.M)) == 10, 'Wrong typed caller count.')
    require(imports(S) == ['ZFCinPA.InternalInterpretation','ZFCinPA.RawFormQuotation','BusyBeaver.ZFC.WellFoundedPart'] and imports(A) == [MODULE], 'Changed direct imports.')
    for q in (S,A):
        require(not re.search(r'\b(sorry|admit|native_decide)\b',q.read_text()), 'Untrusted proof shortcut.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)',q.read_text()), 'Changed proof limits.')
    reused=b['reused_modules']; providers=b['providers']; tools=b['toolchain_providers']
    require({q['module'] for q in reused} == PROJECTS and len(reused) == 27, 'Wrong project providers.')
    def historical_pin(e,path,expected):
        resolved=pin(path,expected)
        require(e['before'].get(str(resolved)) == expected and e['after'].get(str(resolved)) == expected, 'Selected ancestor pair absent from before/after.')
    for q in reused:
        key=q['selected_from']; e=evidence[key]; old=parent_rows[key][q['module']]
        require(all(old[k] == q[k] for k in ('source','source_sha256','object','object_sha256')), 'Wrong selected source/object pair.')
        pin(q['source'],q['source_sha256']);pin(q['object'],q['object_sha256'])
        if not old.get('selected_fresh'):
            historical_pin(e,q['source'],q['source_sha256']);historical_pin(e,q['object'],q['object_sha256'])
            firsts=[r for r in e['actual_first_providers'] if r['module'] == q['module']]
            require(len(firsts) == 1, 'Missing unique selected actual-first provider.')
            r=firsts[0]; actual=r.get('resolved',r['actual_first'])
            require(Path(actual).resolve() == Path(q['object']).resolve() and Path(r['actual_first']).resolve() == Path(q['object']).resolve() and r['sha256'] == q['object_sha256'], 'Wrong selected actual-first provider.')
        # Shared actual parent identities must agree even when only one supplies the current pair.
        for other in parent_rows.values():
            if q['module'] in other:
                require(all(other[q['module']][k] == q[k] for k in ('source_sha256','object_sha256')), 'Conflicting shared parent provider.')
    require(providers == core['providers'] == quotation['providers'] and tools == core['toolchain_providers'] == quotation['toolchain_providers'], 'Changed inherited external/tools.')
    for q in providers:
        historical_pin(core,q['source'],q['source_sha256']);historical_pin(core,q['object'],q['object_sha256'])
    require({q['module'] for q in tools} == {'Init','Lean.Elab.Tactic.Omega'}, 'Wrong tool boundary.')
    for q in tools:
        historical_pin(core,q['object'],q['object_sha256']);pin(q['toolchain_reference'],q['toolchain_reference_sha256'])
        old=next(r for r in binary['toolchain_providers'] if r['module'] == q['module'])
        require(Path(old['object']).resolve() == Path(q['object']).resolve() and old['object_sha256'] == q['object_sha256'], 'Different binary tool identity.')
    C=pin(b['compiler']['path'],b['compiler']['sha256'])
    require(b['dependencies'] == core['dependencies'] == quotation['dependencies'] and D == Path(b['dependencies']['root']).resolve(), 'Wrong dependency root.')
    pin(D/'lake-manifest.json',b['dependencies']['lake_manifest_sha256'])
    def dependency_state():
        state = {}
        for name in ('Foundation', 'Mathlib'):
            d = b['dependencies'][name]; root = Path(d['path'])
            head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
            dirty = subprocess.check_output(['git', '-C', str(root), 'status', '--porcelain', '--untracked-files=no'], text=True)
            require(head == d['pin'] and d['tracked_clean'] and not dirty, 'Changed dependency source state: ' + name)
            state[name] = dict(path=str(root), pin=head, tracked_clean=True)
        return state
    dep_state = dependency_state()
    project_map = {q['module']: q for q in reused}; external = set(b['direct_external_boundaries']); seen = set(); found_external = set()
    def visit(m):
        if m in external:
            found_external.add(m); return
        require(m in project_map, 'Unselected imported project: ' + m)
        if m in seen:
            return
        seen.add(m)
        for child in imports(project_map[m]['source']):
            visit(child)
    for m in imports(S):
        visit(m)
    require(seen == PROJECTS and found_external == external, 'Wrong actual project/external DFS.')
    namespace = Path(b['namespace_overlay']['source']).resolve()
    require(namespace.is_dir(), 'Missing historical Foundation namespace overlay.')
    libs = [Path(x) for x in b['libraries']]
    require(all(q.is_dir() for q in libs) and b['libraries'] == core['LEAN_PATH'].split(os.pathsep)[1:], 'Wrong existing library roots.')
    W.mkdir(parents=True, exist_ok=True); cache = W/'cache'; cache.mkdir(); snaps = W/'sources'; snaps.mkdir()
    (cache/'Foundation').symlink_to(namespace, target_is_directory=True)
    for q in reused:
        dest = cache/rel(q['module']); dest.parent.mkdir(parents=True, exist_ok=True); dest.symlink_to(Path(q['object']).resolve())
    ss = snaps/rel(MODULE, '.lean'); ss.parent.mkdir(parents=True); shutil.copyfile(S, ss)
    aa = snaps/'Audit.lean'; shutil.copyfile(A, aa)
    pin(ss, SOURCE_SHA); pin(aa, AUDIT_SHA)
    search = [cache, *libs, C.parent.parent/'lib/lean']
    def first(m):
        q = next((root/rel(m) for root in search if (root/rel(m)).is_file()), None)
        require(q is not None, 'Missing actual first provider: ' + m)
        return q.resolve()
    def provider_check():
        rows = []
        for q in reused + providers + tools:
            actual = first(q['module'])
            require(actual == Path(q['object']).resolve() and sha(actual) == q['object_sha256'], 'Wrong actual first provider: ' + q['module'])
            rows.append(dict(module=q['module'], actual_first=str(actual), sha256=sha(actual)))
        return rows
    actual = provider_check(); env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [cache, *libs])), LEAN_NUM_THREADS='1')
    record = dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING',prepare_only=args.prepare_only,
        scope='The three explicit closed native quotient/WF formula codes satisfy InternalInterpretation.Good in arbitrary IΣ1 models. No unclosed-code equality, semantic bridge, domain nonemptiness, interpreted native axioms, consistency transport, or PA machine endpoint.',
        source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)),audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),
        boundary=dict(path=str(B),sha256=BOUNDARY_SHA),parent_summaries=parent_summaries,parent_snapshots=parent_snapshots,
        compiler=b['compiler'],compiler_version_query_performed=False,reused_modules=reused,providers=providers,toolchain_providers=tools,
        actual_first_providers=actual,exact_project_prerequisite_count=27,exact_project_import_closure=sorted(seen),
        direct_external_boundaries=sorted(external),inherited_extra_external_modules=b['inherited_extra_external_modules'],dependencies=b['dependencies'],
        namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace),whole_namespace_independently_attested=False),
        before=dict(tracked),commands=[],fresh_modules=[],LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS='1',memory_mebibytes=4096,
        shared_timeout_seconds=120,global_option_overrides=[],dependency_build=False,downloads=False,whole_dependency_cache_attested=False)
    def save():
        (W/'verification.json').write_text(json.dumps(record, ensure_ascii=False, indent=2)+'\n')
    def post():
        record['after'] = {q: sha(q) for q in tracked}
        require(record['after'] == record['before'], 'Input changed during check.')
        require(provider_check() == actual and dependency_state() == dep_state, 'Provider/dependency postcheck failed.')
        for q in record['fresh_modules']:
            require(first(q['module']) == Path(q['path']).resolve() and sha(q['path']) == q['sha256'], 'Fresh object/first provider changed.')
        record['all_input_provider_postchecks'] = True
    save()
    try:
        if args.prepare_only:
            post(); save(); print(W/'verification.json'); return
        deadline = time.monotonic() + 120
        def run(label, file, obj=None):
            remaining = deadline-time.monotonic(); require(remaining > 0, 'Shared deadline exhausted.')
            cmd = [str(C), '-j1', '-M4096', '--root='+str(snaps)] + (['-o', str(obj)] if obj else []) + [str(file)]
            started = time.monotonic(); proc = subprocess.Popen(cmd, cwd=snaps, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
            timed_out = False; interrupted = None
            try:
                data, _ = proc.communicate(timeout=remaining)
            except BaseException as ex:
                timed_out = isinstance(ex, subprocess.TimeoutExpired); interrupted = None if timed_out else type(ex).__name__
                try: os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                data, _ = proc.communicate()
            out = data.decode(errors='replace'); log = W/(label+'.log'); log.write_text(out)
            record['commands'].append(dict(label=label, command=cmd, seconds=time.monotonic()-started, exit_code=proc.returncode, timed_out=timed_out, interrupted=interrupted, output=out, log=str(log), log_sha256=sha(log)))
            save(); require(not timed_out and interrupted is None and proc.returncode == 0, label+' failed; exact log preserved.')
            require('sorryAx' not in out and "declaration uses 'sorry'" not in out, 'Untrusted declaration in output.')
            return out
        obj = cache/rel(MODULE); require(not obj.exists(), 'Fresh target already present.')
        run('source', ss, obj)
        fresh = dict(module=MODULE, path=str(obj), sha256=sha(obj), source_sha256=SOURCE_SHA)
        record['fresh_modules'] = [fresh]
        record['source_pass_object'] = dict(fresh, source_command_index=0)
        require(first(MODULE) == obj.resolve(), 'Fresh source object is not first provider.')
        record['fresh_first_provider_before_audit'] = dict(module=MODULE, path=str(first(MODULE)), sha256=sha(first(MODULE)))
        record['source_object_recorded_before_audit'] = True; save()
        out = run('audit', aa); rr = reports(out)
        require([q['name'] for q in rr] == ['LeanProofs.ZFCinPA.NativeWFClosedParameters.'+n for n in PROBES], 'Wrong ordered actual axiom reports.')
        require(all(set(q['axioms']) <= STANDARD for q in rr), 'Nonstandard axiom report.')
        post(); record.update(status='PASS', named_axiom_probes=7, callers=10, axiom_reports=rr, only_standard_axioms=True,
            all_fresh_objects_unchanged_after_audit=True, warnings=sum(c['output'].count('warning:') for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL', error=repr(ex))
        try: post()
        except BaseException as post_error: record['postcheck_error'] = repr(post_error)
        save(); raise
    save(); print(W/'verification.json')

if __name__ == '__main__':
    main()
