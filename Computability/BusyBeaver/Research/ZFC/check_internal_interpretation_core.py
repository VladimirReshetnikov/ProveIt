#!/usr/bin/env python3
"""Fresh reduced-import InternalInterpretation; source then seven-probe/13-client audit.
Reuse three checked projects and the refresh record's explicit external cache boundary.
Shared120s, -j1, -M4096; no proof-option overrides, version query, build or download.
Prepare-only records exact providers and snapshots without invoking Lean.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time

HERE = Path(__file__).resolve().parent
MODULE = 'ZFCinPA.InternalInterpretation'
SOURCE_SHA = '60bdb604d5aa34402a3a050a397a4b46b7e2892ae1a14875a806caa9dfac3720'
AUDIT_SHA = 'bf8b6d101f41c2ef8579c8285926f90744b3217951faceddac15e26fe8174d08'
BOUNDARY_SHA = 'cc6411fad7b900a595a27c7a6771405bcf151bfcd2cb8dc4a7566d6f2863105c'
PARENT_SHA = '83534a1aeeeaa97881e4632156cad75120be730bd7d77761d3e460e87a4fca55'
PROJECTS = {'ZFCinPA.Instances', 'BoundedPAConsistency.InternalRelativization', 'ZFCinPA.SetRelativization'}
PROBES = ['interp_neg', 'interp_shift', 'interp_subst', 'interp_free', 'derivable_iSet', 'provable_interp', 'provable_falsum_of_interp']
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
    p.add_argument('--source', type=Path, default=HERE.parents[3]/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/InternalInterpretation.lean')
    p.add_argument('--audit', type=Path, default=HERE/'internal_interpretation_core_audit.lean')
    p.add_argument('--boundary', type=Path, default=HERE/'results/internal-interpretation-core-boundary.json')
    p.add_argument('--parent-evidence', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--prepare-only', action='store_true')
    args = p.parse_args()
    require(__debug__, 'Python -O is unsupported.')
    R, D, W = args.repo.resolve(), args.dependency_root.resolve(), args.output.resolve()
    S, A, B = args.source.resolve(), args.audit.resolve(), args.boundary.resolve()
    require(not W.is_relative_to(R) and not W.is_relative_to(D), 'Output must be outside maintained/dependency roots.')
    require(not W.exists() or (W.is_dir() and not any(W.iterdir())), 'Fresh output required.')
    require(sha(S) == SOURCE_SHA and sha(A) == AUDIT_SHA and sha(B) == BOUNDARY_SHA, 'Changed source/audit/boundary.')
    b = json.loads(B.read_text())
    # Newly published source/history descriptors are repository-relative; checked providers retain their historical paths.
    for role, keys in [('parent', ['path']), ('original_source', ['path', 'archive']), ('supplied_audit', ['path', 'archive']), ('source', ['path'])]:
        for key in keys:
            value = Path(b[role][key])
            require(not value.is_absolute() and '..' not in value.parts, 'Unsafe maintained descriptor path.')
            b[role][key] = str(R/value)
    E = (args.parent_evidence or Path(b['parent']['path'])).resolve()
    require(sha(E) == PARENT_SHA == b['parent']['sha256'], 'Wrong exact refresh PASS.')
    e = json.loads(E.read_text())
    require(e['status'] == 'PASS' and (e['named_axiom_probes'], e['callers']) == (19, 24), 'Wrong refresh census/status.')
    require(e['before'] == e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'], 'Incomplete historical PASS.')
    require([q['label'] for q in e['commands']] == ['base-source', 'base-audit', 'set-source', 'set-audit'], 'Wrong historical command order.')
    require(all(q['exit_code'] == 0 and not q['timed_out'] for q in e['commands']), 'Historical command failed.')
    tracked = {}
    def pin(path, expected):
        q = Path(path).resolve()
        require(q.is_file() and sha(q) == expected, 'Changed or absent input: ' + str(q))
        require(str(q) not in tracked or tracked[str(q)] == expected, 'Conflicting input identity: ' + str(q))
        tracked[str(q)] = expected
        return q
    for path, expected in e['before'].items():
        pin(path, expected)
    for q in (Path(__file__).resolve(), S, A, B, E):
        pin(q, sha(q))
    for key in ('original_source', 'supplied_audit'):
        q = b[key]
        pin(q['path'], q['sha256']); pin(q['archive'], q['sha256'])
    require(Path(b['original_source']['path']).is_relative_to(R), 'Wrong maintained source root.')
    short_probes = ['InternalInterpretation.' + n for n in PROBES]
    require(re.findall(r'^#print axioms (\S+)$', A.read_text(), re.M) == short_probes, 'Wrong ordered audit probes.')
    require(re.findall(r'^#print axioms (\S+)$', Path(b['supplied_audit']['archive']).read_text(), re.M) == short_probes, 'Supplied audit changed.')
    require(len(re.findall(r'^example\b', A.read_text(), re.M)) == 13, 'Wrong typed caller count.')
    require(imports(S) == ['ZFCinPA.SetRelativization', 'BoundedPAConsistency.InternalRelativization'] and imports(A) == [MODULE], 'Changed direct imports.')
    for q in (S, A):
        require(not re.search(r'\b(sorry|admit|native_decide)\b', q.read_text()), 'Untrusted proof shortcut.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)', q.read_text()), 'Changed proof limits.')
    reused = b['reused_modules']; providers = b['providers']; tools = b['toolchain_providers']
    require({q['module'] for q in reused} == PROJECTS and len(reused) == 3, 'Wrong project provider set.')
    parent_rows = {q['module']: q for q in e['reused_modules']}
    for source, audit_command in zip(e['sources'], [e['commands'][1], e['commands'][3]]):
        f = next(q for q in e['fresh_modules'] if q['module'] == source['module'])
        require(f['source_sha256'] == source['source_sha256'], 'Historical fresh/source mismatch.')
        parent_rows[source['module']] = dict(source=source['source'], source_sha256=source['source_sha256'], object=f['path'], object_sha256=f['sha256'])
        for k, h in [('source', 'source_sha256'), ('snapshot', 'source_sha256'), ('audit', 'audit_sha256'), ('audit_snapshot', 'audit_sha256')]:
            pin(source[k], source[h])
        old_probes = re.findall(r'^#print axioms (\S+)$', Path(source['audit_snapshot']).read_text(), re.M)
        rr = reports(audit_command['output'])
        require([q['name'] for q in rr] == old_probes == source['probes'], 'Historical raw probe mismatch.')
        require(all(set(q['axioms']) <= STANDARD for q in rr), 'Historical nonstandard axioms.')
        require(len(re.findall(r'^example\b', Path(source['audit_snapshot']).read_text(), re.M)) == source['callers'], 'Historical typed census mismatch.')
    for q in reused:
        old = parent_rows[q['module']]
        require(all(q[k] == old[k] for k in ('source', 'source_sha256', 'object', 'object_sha256')), 'Wrong selected checked pair.')
    require(providers == e['providers'] and tools == e['toolchain_providers'], 'External boundary differs from checked parent.')
    for q in reused + providers:
        pin(q['source'], q['source_sha256']); pin(q['object'], q['object_sha256'])
    require({q['module'] for q in tools} == {'Init', 'Lean.Elab.Tactic.Omega'}, 'Wrong tool boundary.')
    for q in tools:
        pin(q['object'], q['object_sha256']); pin(q['toolchain_reference'], q['toolchain_reference_sha256'])
    C = pin(b['compiler']['path'], b['compiler']['sha256'])
    require(b['compiler'] == e['compiler'], 'Wrong recorded compiler identity.')
    require(b['dependencies'] == e['dependencies'] and D == Path(b['dependencies']['root']).resolve(), 'Dependency root differs.')
    pin(D/'lake-manifest.json', b['dependencies']['lake_manifest_sha256'])
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
    require(all(q.is_dir() for q in libs) and b['libraries'] == e['LEAN_PATH'].split(os.pathsep)[1:], 'Wrong existing library roots.')
    W.mkdir(parents=True, exist_ok=True); cache = W/'cache'; cache.mkdir(); snaps = W/'sources'; snaps.mkdir()
    (cache/'Foundation').symlink_to(namespace, target_is_directory=True)
    for q in reused:
        dest = cache/rel(q['module']); dest.parent.mkdir(parents=True, exist_ok=True); dest.symlink_to(Path(q['object']).resolve())
    ss = snaps/rel(MODULE, '.lean'); ss.parent.mkdir(parents=True); shutil.copyfile(S, ss)
    aa = snaps/'Audit.lean'; shutil.copyfile(A, aa)
    supplied = snaps/'SuppliedAudit.lean'; shutil.copyfile(b['supplied_audit']['archive'], supplied)
    pin(ss, SOURCE_SHA); pin(aa, AUDIT_SHA); pin(supplied, b['supplied_audit']['sha256'])
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
    record = dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING', prepare_only=args.prepare_only,
        scope='Reduced-import represented interpretation core; arbitrary internal IΣ1 formula/derivation codes. Good, interpreted axioms and domain nonemptiness remain hypotheses; no native R3 closure.',
        source=dict(path=str(S), sha256=SOURCE_SHA, snapshot=str(ss)), audit=dict(path=str(A), sha256=AUDIT_SHA, snapshot=str(aa)),
        supplied_audit=dict(b['supplied_audit'], snapshot=str(supplied), separately_executed=False, all_seven_probes_retained_in_selected_audit=True),
        source_variant='Original public ABI and proof bodies with private literal arity lemma and narrower imports; original maintained source retained.',
        boundary=dict(path=str(B), sha256=BOUNDARY_SHA), parent=dict(path=str(E), sha256=PARENT_SHA),
        parent_schema=dict(b['legacy_parent_scope'], historical_version_query=e['compiler_version_query_performed']),
        compiler=e['compiler'], compiler_version_query_performed=False, reused_modules=reused, providers=providers, toolchain_providers=tools,
        actual_first_providers=actual, exact_project_prerequisite_count=3, exact_project_import_closure=sorted(seen),
        direct_external_boundaries=sorted(external), discovery_anchor_modules=b['discovery_anchor_modules'], dependencies=b['dependencies'],
        namespace_overlay=dict(target=str(cache/'Foundation'), source=str(namespace), whole_namespace_independently_attested=False),
        before=dict(tracked), commands=[], fresh_modules=[], LEAN_PATH=env['LEAN_PATH'], LEAN_NUM_THREADS='1', memory_mebibytes=4096,
        shared_timeout_seconds=120, global_option_overrides=[], dependency_build=False, downloads=False, whole_dependency_cache_attested=False)
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
        require([q['name'] for q in rr] == ['LeanProofs.ZFCinPA.InternalInterpretation.'+n for n in PROBES], 'Wrong ordered actual axiom reports.')
        require(all(set(q['axioms']) <= STANDARD for q in rr), 'Nonstandard axiom report.')
        post(); record.update(status='PASS', named_axiom_probes=7, callers=13, axiom_reports=rr, only_standard_axioms=True,
            all_fresh_objects_unchanged_after_audit=True, warnings=sum(c['output'].count('warning:') for c in record['commands']))
    except BaseException as ex:
        record.update(status='FAIL', error=repr(ex))
        try: post()
        except BaseException as post_error: record['postcheck_error'] = repr(post_error)
        save(); raise
    save(); print(W/'verification.json')

if __name__ == '__main__':
    main()
