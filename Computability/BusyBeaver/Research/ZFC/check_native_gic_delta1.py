#!/usr/bin/env python3
"""Unchanged NativeGicDelta1, seven probes/ten typed callers.
Four selected project pairs; inherited external cache is explicitly bounded.
Shared120s, -j1, -M4096, process-group cleanup; no version query/build/download.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, signal, subprocess, time

HERE = Path(__file__).resolve().parent
MODULE = 'ZFCinPA.NativeGicDelta1'
SOURCE_SHA = '9abb4d641e4d3db586c25f525d0efea98da466bc4497f5c11c9f0393078ce861'
AUDIT_SHA = 'c2f68a401f223a00f59dfa1f7c3e0ad2a23d365a9d2a541bef1c099441b7a0b7'
BOUNDARY_SHA = '1027022495897a04e703a80319387c6eee67b32a5d4224ac1709d263553c8b7b'
PARENT_SHA = 'c6ed6c6bd40da28a3460778686f32cd969fd5695ce89187a72efe19e23c2fadd'
PROJECTS = {'ZFCinPA.ReplacementDelta1', 'ZFCinPA.SeparationDelta1', 'ZFCinPA.Instances', 'ZFCinPA.SchemaClosure'}
PROBES = ['gicBody_quote', 'gicBodyVal_eq', 'gicBodyVal_quote', 'le_gicBodyVal_quote', 'gicBodyVal.defined', 'GicR.defined', 'gicTheory_delta1']
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
    p.add_argument('--source', type=Path, default=HERE.parents[3]/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeGicDelta1.lean')
    p.add_argument('--audit', type=Path, default=HERE/'native_gic_delta1_audit.lean')
    p.add_argument('--boundary', type=Path, default=HERE/'results/native-gic-delta1-boundary.json')
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
    b = json.loads(B.read_text()); tracked = {}
    def pin(path, expected):
        q = Path(path).resolve()
        require(q.is_file() and sha(q) == expected, 'Changed or absent input: ' + str(q))
        require(str(q) not in tracked or tracked[str(q)] == expected, 'Conflicting input identity: ' + str(q))
        tracked[str(q)] = expected
        return q
    for q in (Path(__file__).resolve(), S, A, B):
        pin(q, sha(q))
    E = pin(args.parent_evidence or b['parent']['path'], PARENT_SHA)
    require(b['parent']['sha256'] == PARENT_SHA, 'Wrong parent boundary.')
    e = json.loads(E.read_text())
    require(e['status'] == 'PASS' and (e['named_axiom_probes'],e['callers']) == (25,18), 'Wrong parent status/census.')
    require(e['before'] == e['after'] and e['all_input_provider_postchecks'] and e['all_fresh_objects_unchanged_after_audit'] and e['only_standard_axioms'], 'Incomplete parent evidence.')
    require([q['label'] for q in e['commands']] == ['source','audit'] and all(q['exit_code'] == 0 and not q['timed_out'] for q in e['commands']), 'Failed parent commands.')
    require(all(e['compiler'][k] == b['compiler'][k] for k in ('path','sha256','version')), 'Different parent compiler.')
    sp = pin(e['source']['snapshot'],e['source']['sha256']); ap = pin(e['audit']['snapshot'],e['audit']['sha256'])
    names = re.findall(r'^#print axioms (\S+)$', ap.read_text(), re.M); rr = reports(e['commands'][1]['output'])
    require(len(names) == 25 and [q['name'] for q in rr] == names and all(set(q['axioms']) <= STANDARD for q in rr), 'Wrong parent raw reports.')
    require(len(re.findall(r'^example\b',ap.read_text(),re.M)) == 18, 'Wrong parent callers.')
    parent_summaries = dict(constructible=dict(path=str(E),sha256=PARENT_SHA,selected_modules=sorted(PROJECTS),all_ancestor_inputs_rehashed=False,unselected_fresh_objects_rehashed=False,actual_first_capture_present=True,preaudit_capture_present=False,scope=b['scope']))
    parent_snapshots = [dict(source=str(sp),source_sha256=e['source']['sha256'],audit=str(ap),audit_sha256=e['audit']['sha256'])]
    pin(b['maintained_source']['path'], SOURCE_SHA)
    pin(b['supplied_audit']['path'], b['supplied_audit']['sha256'])
    require(re.findall(r'^#print axioms (\S+)$', A.read_text(), re.M) == ['LeanProofs.ZFCinPA.'+n for n in PROBES], 'Wrong ordered audit probes.')
    require(len(re.findall(r'^example\b', A.read_text(), re.M)) == 10, 'Wrong typed caller count.')
    require(imports(S) == ['ZFCinPA.ReplacementDelta1'] and imports(A) == [MODULE], 'Changed direct imports.')
    for q in (S,A):
        require(not re.search(r'\b(sorry|admit|native_decide)\b', q.read_text()), 'Untrusted proof shortcut.')
        require(not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)', q.read_text()), 'Changed proof limits.')
    reused = b['reused_modules']; providers = b['providers']; tools = b['toolchain_providers']
    require({q['module'] for q in reused} == PROJECTS and len(reused) == 4, 'Wrong project providers.')
    def old_pair(e, q):
        rows = [r for r in e['reused_modules'] if r['module'] == q['module']]
        require(len(rows) == 1 and all(rows[0][k] == q[k] for k in ('source','source_sha256','object','object_sha256')), 'Wrong selected historical pair.')
    def historical_pin(e, path, expected):
        resolved = pin(path, expected)
        require(e['before'].get(str(resolved)) == expected and e['after'].get(str(resolved)) == expected, 'Selected pair missing from parent before/after.')
    for q in reused:
        old_pair(e,q)
        for path,expected in [(q['source'],q['source_sha256']),(q['object'],q['object_sha256'])]:
            historical_pin(e,path,expected)
        rows = [r for r in e['actual_first_providers'] if r['module'] == q['module']]
        require(len(rows) == 1 and Path(rows[0]['resolved']).resolve() == Path(q['object']).resolve() and Path(rows[0]['actual_first']).resolve() == Path(q['object']).resolve() and rows[0]['sha256'] == q['object_sha256'], 'Wrong selected historical first provider.')
    require({q['module'] for q in providers} == set(b['direct_external_boundaries']) | set(b['inherited_extra_external_modules']) and len(providers) == 5, 'Wrong external selection.')
    for q in providers:
        require(q == next(r for r in e['providers'] if r['module'] == q['module']), 'Wrong historical external pair.')
        historical_pin(e,q['source'],q['source_sha256']); historical_pin(e,q['object'],q['object_sha256'])
    require(tools == e['toolchain_providers'] and {q['module'] for q in tools} == {'Init','Lean.Elab.Tactic.Omega'}, 'Wrong tools.')
    for q in tools:
        historical_pin(e,q['object'],q['object_sha256']); pin(q['toolchain_reference'],q['toolchain_reference_sha256'])
    C = pin(b['compiler']['path'],b['compiler']['sha256'])
    require(b['dependencies'] == e['dependencies'] and D == Path(b['dependencies']['root']).resolve(), 'Wrong dependency root.')
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
    require(all(q.is_dir() for q in libs) and b['libraries'] == e['LEAN_PATH'].split(os.pathsep)[1:], 'Wrong existing library roots.')
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
    record = dict(status='PREPARED_NOT_BUILT' if args.prepare_only else 'RUNNING', prepare_only=args.prepare_only,
        scope='Unchanged NativeGicDelta1: body quotation, raw-code graph and recognizer in arbitrary IΣ1 models, and Delta1 GIC theory. No NativeTheory/NativeInterp/NativeFixed check or internal ZF axiom transport.',
        source=dict(path=str(S),sha256=SOURCE_SHA,snapshot=str(ss)), audit=dict(path=str(A),sha256=AUDIT_SHA,snapshot=str(aa)),
        boundary=dict(path=str(B),sha256=BOUNDARY_SHA), parent_summaries=parent_summaries, parent_snapshots=parent_snapshots,
        compiler=b['compiler'], compiler_version_query_performed=False, reused_modules=reused, providers=providers, toolchain_providers=tools,
        actual_first_providers=actual, exact_project_prerequisite_count=4, exact_project_import_closure=sorted(seen),
        direct_external_boundaries=sorted(external), inherited_extra_external_modules=b['inherited_extra_external_modules'], dependencies=b['dependencies'],
        namespace_overlay=dict(target=str(cache/'Foundation'),source=str(namespace),whole_namespace_independently_attested=False),
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
        require([q['name'] for q in rr] == ['LeanProofs.ZFCinPA.'+n for n in PROBES], 'Wrong ordered actual axiom reports.')
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
