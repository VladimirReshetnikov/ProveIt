#!/usr/bin/env python3
"""Bounded exact245 unbounded register-box proof; eight project providers, no rebuild.
The Pulse PASS record pin must be frozen after the root's successful pulse run.
Prepare-only performs no compiler or version invocation. Proof mode compiles
only Routing245Boxes and its focused audit, serially, with a fresh output object.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, time

MODULE = 'BusyBeaver.ZFC.Routing245Boxes'
PREFIX = 'SetTheory.BusyBeaver.ZFC.Routing245Boxes.'
SOURCE_SHA = '5fda8586b4356485e0ddc6acbc359e68638d02c245e6bce13fafd552da293127'
AUDIT_SHA = '37f1334add4d128ef3df134903c9158584b2e1a60f53efcc6567e5841a1cd2f8'
PULSE_RECORD_SHA = 'c756bf41b8f2f778d0c6c21e8de0e54a3625cc69253607cb7e0f6fe1c3c605fb'
BOXES_RECORD_SHA = 'bd0671838ff39bbc6d3009c420858747b868988e17fe41b32e8e88ba8db8974a'
EXPECTED = {
    'BusyBeaver.Core': ('436336133fa107c62eb00322333ec9451a0705964bd2b62fce3f44ce848672a6', '2c18d0fc971038cdd3cf5998857f56a88ea1cf33cd11f90f6794866fcc2e1148'),
    'BusyBeaver.ZFC.FiniteZipper': ('f7b41631975f0c243bcb6e48a6c566adde0866fb93f7105571e310c18db45066', 'bfbfb31d4cd560b52a65a832777d64f544dc6a1bbbb080829cc1465881d44101'),
    'BusyBeaver.ZFC.ZipperRuns': ('fc8f39330f6551fb2b29db22127efbb361dd421290b47ca95d1088d7104a3d48', 'f6280bb230bb5f816c27fcd7789aa16a3890d5a0ac3c0d74bd4ac9a19006e8b6'),
    'BusyBeaver.ZFC.TablePerm252': ('d216d7292acf690095048024e2cae2575195ded015acf8e235261b8152e74bd0', '62f26b312a448576ae3b83dbeb336a844fbcf9e1341e67aec79114e553dd67c3'),
    'BusyBeaver.ZFC.RegisterBoxesPerm252': ('da0a5c460aba89b9d46dc794fad70a98ac441238ed26c5f7287fa4797a0bd5e7', 'ca74f3f602f975958c6c316071dfc151d1b73d4dcc33c34ce19bc8b07fe76c3e'),
    'BusyBeaver.ZFC.RegisterMarkPerm252': ('c646007b54f2d32242f593a60eb770834f3e085a03ee60beb1275aebb796ce41', '6d661f5afac61d31ae82fe20e5c2420216fe2bdb866dbabf5572455061df200c'),
}
PROBES = ['carryBits_snoc', 'carry_file', 'return_separator', 'positive_decrement_zip', 'rollback_file', 'zero_decrement_zip', 'carry_end', 'shift_suffix', 'increment_zip', 'positive_decrement_boundary', 'positive_decrement', 'zero_decrement', 'increment', 'following_nonempty']
CALLERS = 19
TIMEOUT = 120

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--pulse-evidence', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--source', type=Path)
p.add_argument('--audit', type=Path)
p.add_argument('--prepare-only', action='store_true')
a = p.parse_args()
if not __debug__:
    p.error('Assertions must remain enabled.')
sha = lambda path: hashlib.sha256(Path(path).read_bytes()).hexdigest()
R = a.repo.resolve()
W = a.output.resolve()
assert not W.is_relative_to(R) and (not W.exists() or not any(W.iterdir()))
assert PULSE_RECORD_SHA != 'PENDING_SUCCESSFUL_PULSE_RECORD', 'Freeze successful pulse evidence before preparation or compilation.'
S = a.source.resolve() if a.source else Path('/tmp/zfc-routing245-lean/boxes/source-v2/Routing245Boxes.lean')
A = a.audit.resolve() if a.audit else Path('/tmp/zfc-routing245-lean/boxes/Audit.lean')
assert sha(S) == SOURCE_SHA and sha(A) == AUDIT_SHA
E = a.pulse_evidence.resolve()
BOXES = R / 'Computability/BusyBeaver/Research/ZFC/results/prefix246-boxes-verification.json'
assert sha(E) == PULSE_RECORD_SHA and sha(BOXES) == BOXES_RECORD_SHA
parent, boxes = json.loads(E.read_text()), json.loads(BOXES.read_text())
for d in (parent, boxes):
    assert d['status'] == 'PASS' and d['only_standard_axioms']
    assert d['all_input_provider_postchecks'] and d['all_fresh_objects_unchanged_after_audit']
    assert len(d['commands']) == 2 and all(q['exit_code'] == 0 for q in d['commands'])
    assert [q['label'] for q in d['commands']] == ['source', 'audit']
    assert d['before'] == d['after']
    assert d['source_object_recorded_before_audit']
C = Path(parent['compiler']['path']).resolve()
assert parent['compiler']['sha256'] == boxes['compiler']['sha256'] == sha(C)
assert parent['compiler']['version'] == boxes['compiler']['version']
version = parent['compiler']['version']
toolroot = C.parent.parent / 'lib/lean'

def imports(path):
    text = Path(path).read_text()
    return re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', text, re.M)

assert imports(S) == ['BusyBeaver.ZFC.Routing245Pulse', 'BusyBeaver.ZFC.RegisterMarkPerm252']
assert imports(A) == [MODULE]
assert re.findall(r'^#print axioms (\S+)$', A.read_text(), re.M) == [PREFIX + n for n in PROBES]
assert len(re.findall(r'^example\b', A.read_text(), re.M)) == CALLERS
# Reject new unchecked proof exits and enlarged elaboration budgets.
for f in (S, A):
    assert not re.search(r'\b(sorry|admit|native_decide)\b', f.read_text())
    assert not re.search(r'set_option\s+(maxHeartbeats|maxRecDepth)', f.read_text())
pool = {q['module']: q for q in boxes['reused_modules']}
selected = {}
for m, (source_sha, object_sha) in EXPECTED.items():
    q = pool[m]
    source = R / 'Computability/BusyBeaver/Lean' / Path(m.replace('.', '/')).with_suffix('.lean')
    obj = Path(q['object']).resolve()
    assert q['source_sha256'] == source_sha == sha(source)
    assert q['object_sha256'] == object_sha == sha(obj)
    historical = next(x for x in boxes['actual_first_providers'] if x['module'] == m)
    assert historical['sha256'] == object_sha
    assert Path(historical['actual_first']).resolve() == obj
    selected[m] = dict(module=m, source=str(source), source_sha256=source_sha,
                       object=str(obj), object_sha256=object_sha, evidence=str(BOXES))
# Recheck the exact pulse source-PASS object recorded before its audit.
assert parent['source_object_recorded_before_audit']
fresh = [q for q in parent['fresh_modules'] if q['module'] == 'BusyBeaver.ZFC.Routing245Pulse']
assert len(fresh) == 1
q = fresh[0]
pulse_source = Path(parent['source']['path']).resolve()
pulse_snapshot = Path(parent['source']['snapshot']).resolve()
assert q['source_sha256'] == parent['source']['sha256'] == sha(pulse_source) == sha(pulse_snapshot)
pulse_object = Path(q['path']).resolve()
assert sha(pulse_object) == q['sha256']
assert parent['source_pass_object'] == q
assert parent['fresh_first_provider_before_audit']['sha256'] == q['sha256']
assert Path(parent['fresh_first_provider_before_audit']['path']).resolve() == pulse_object
selected[q['module']] = dict(module=q['module'], source=str(pulse_source),
    source_sha256=sha(pulse_source), object=str(pulse_object), object_sha256=sha(pulse_object), evidence=str(E))
# Every old provider used to check the pulse must agree with the selected closure.
for q in parent['reused_modules']:
    if q['module'] in EXPECTED:
        assert (q['source_sha256'], q['object_sha256']) == EXPECTED[q['module']]
# Reuse the exact table provider already used by the successful pulse proof.
pt = [q for q in parent['reused_modules'] if q['module'] == 'BusyBeaver.ZFC.TableRouting245']
assert len(pt) == 1
q = pt[0]
table_source = Path(q['source']).resolve()
table_object = Path(q['object']).resolve()
assert sha(table_source) == q['source_sha256'] and sha(table_object) == q['object_sha256']
selected[q['module']] = dict(module=q['module'], source=str(table_source),
    source_sha256=q['source_sha256'], object=str(table_object), object_sha256=q['object_sha256'], evidence=q['evidence'])
# Preserve and verify the evidence record that supplied that table object.
TE = Path(q['evidence']).resolve()
te_pin = [e for e in parent['provider_evidence'] if Path(e['path']).resolve() == TE]
assert len(te_pin) == 1 and sha(TE) == te_pin[0]['sha256']
te = json.loads(TE.read_text())
assert te['status'] == 'PASS' and te['only_standard_axioms']
assert te['all_input_provider_postchecks'] and te['all_fresh_objects_unchanged_after_audit']
assert te['compiler']['sha256'] == sha(C) and te['compiler']['version'] == version
tf = [x for x in te['fresh_modules'] if x['module'] == q['module']]
assert len(tf) == 1 and tf[0]['sha256'] == q['object_sha256']
assert tf[0]['source_sha256'] == q['source_sha256']
visiting, closure, tool_names = set(), [], {'Init'}
def visit(m):
    if m in closure:
        return
    assert m in selected and m not in visiting
    visiting.add(m)
    for n in imports(selected[m]['source']):
        if n == 'Init' or n.startswith(('Lean.', 'Std.')):
            tool_names.add(n)
        else:
            visit(n)
    visiting.remove(m)
    closure.append(m)
for m in imports(S):
    visit(m)
assert set(closure) == set(selected) and len(closure) == 8
W.mkdir(parents=True, exist_ok=True)
cache, snap = W / 'cache', W / 'sources'
cache.mkdir()
ss = snap / Path(MODULE.replace('.', '/')).with_suffix('.lean')
ss.parent.mkdir(parents=True)
aa = snap / 'Audit.lean'
shutil.copyfile(S, ss)
shutil.copyfile(A, aa)
for m in closure:
    dest = cache / Path(m.replace('.', '/')).with_suffix('.olean')
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.symlink_to(selected[m]['object'])
def first(m):
    rel = Path(m.replace('.', '/')).with_suffix('.olean')
    return next(q / rel for q in (cache, toolroot) if (q / rel).is_file())
actual = []
for m in closure:
    obj = first(m)
    assert sha(obj) == selected[m]['object_sha256']
    actual.append(dict(module=m, actual_first=str(obj), resolved=str(obj.resolve()), sha256=sha(obj)))
assert tool_names == {'Init', 'Lean.Elab.Tactic.Omega'}
tool_pins = {q['module']: q['object_sha256'] for q in boxes['toolchain_providers']}
tools = []
for m in sorted(tool_names):
    ref = toolroot / Path(m.replace('.', '/')).with_suffix('.olean')
    obj = first(m)
    assert obj.resolve() == ref.resolve()
    assert sha(obj) == tool_pins[m]
    tools.append(dict(module=m, object=str(ref), object_sha256=sha(ref), actual_first=str(obj)))
inputs = [Path(__file__).resolve(), S, A, E, TE, BOXES, C, pulse_snapshot, ss, aa]
for q in selected.values():
    inputs += [Path(q['source']), Path(q['object'])]
inputs += [Path(q['object']) for q in tools]
inputs = list(dict.fromkeys(q.resolve() for q in inputs))
before = {str(q): sha(q) for q in inputs}
env = dict(os.environ, LEAN_PATH=str(cache), LEAN_NUM_THREADS='1')
r = dict(status='PREPARED_NOT_BUILT' if a.prepare_only else 'RUNNING', scope=__doc__,
    prepare_only=a.prepare_only, compiler=dict(path=str(C), version=version, sha256=sha(C),
    compiler_version_query_performed=False), source_overridden=a.source is not None,
    audit_overridden=a.audit is not None, source=dict(path=str(S), sha256=sha(S), snapshot=str(ss)),
    audit=dict(path=str(A), sha256=sha(A), snapshot=str(aa)),
    provider_evidence=[dict(path=str(q), sha256=sha(q)) for q in (E, TE, BOXES)],
    reused_modules=[selected[m] for m in closure], exact_project_import_closure=True,
    project_module_count=8, external_project_boundaries=[], toolchain_providers=tools,
    actual_first_providers=actual, actual_direct_tool_imports=sorted(tool_names),
    before=before, commands=[], fresh_modules=[], LEAN_PATH=env['LEAN_PATH'],
    dependency_build=False, downloads=False, per_command_timeout_seconds=TIMEOUT,
    shared_wall_seconds=TIMEOUT)
def save():
    (W / 'verification.json').write_text(json.dumps(r, indent=2) + '\n')
def post():
    after = {str(q): sha(q) for q in inputs}
    assert before == after
    for m in closure:
        assert sha(first(m)) == selected[m]['object_sha256']
    for q in tools:
        assert sha(first(q['module'])) == q['object_sha256']
    r.update(after=after, all_input_provider_postchecks=True)
save()
if a.prepare_only:
    post()
    save()
    print(W / 'verification.json')
    raise SystemExit(0)
deadline = time.monotonic() + TIMEOUT
def run(label, source, obj=None):
    cmd = [str(C), '-j1', '-M4096', '--root=' + str(snap)]
    if obj is not None:
        cmd += ['-o', str(obj)]
    cmd += [str(source)]
    began = time.monotonic()
    remaining = deadline - began
    assert remaining > 0, 'Shared proof wall budget exhausted.'
    try:
        cp = subprocess.run(cmd, cwd=snap, env=env, text=True, capture_output=True, timeout=remaining)
        output, code = cp.stdout + cp.stderr, cp.returncode
    except subprocess.TimeoutExpired as ex:
        def decoded(x):
            return x.decode(errors='replace') if isinstance(x, bytes) else x or ''
        output, code = decoded(ex.stdout) + decoded(ex.stderr) + '\nTIMEOUT\n', -1
    (W / (label + '.log')).write_text(output)
    r['commands'].append(dict(label=label, command=cmd, seconds=time.monotonic() - began,
                              exit_code=code, output=output))
    save()
    assert code == 0 and 'sorryAx' not in output and "declaration uses 'sorry'" not in output, output
    return output
try:
    obj = cache / Path(MODULE.replace('.', '/')).with_suffix('.olean')
    run('source', ss, obj)
    assert obj.is_file() and not obj.is_symlink()
    oh = sha(obj)
    source_object = dict(module=MODULE, path=str(obj), sha256=oh, source_sha256=sha(S))
    r.update(source_object_recorded_before_audit=True, source_pass_object=source_object,
             fresh_modules=[source_object])
    assert first(MODULE).resolve() == obj.resolve()
    r['fresh_first_provider_before_audit'] = dict(module=MODULE, path=str(first(MODULE)), sha256=sha(first(MODULE)))
    save()
    audit_output = run('audit', aa)
    reports = re.findall(r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", audit_output, re.S)
    assert [n for n, _ in reports] == [PREFIX + n for n in PROBES]
    assert all({x.strip() for x in axioms.split(',') if x.strip()} <=
               {'propext', 'Classical.choice', 'Quot.sound'} for _, axioms in reports)
    post()
    assert sha(obj) == oh and sha(first(MODULE)) == oh
    r.update(status='PASS', all_fresh_objects_unchanged_after_audit=True,
             named_axiom_probes=len(PROBES), callers=CALLERS, only_standard_axioms=True,
             warnings={q['label']: q['output'].count('warning:') for q in r['commands']})
except Exception as ex:
    r.update(status='FAIL', error=str(ex))
    try:
        post()
    except Exception as post_error:
        r['postcheck_error'] = str(post_error)
    save()
    raise
save()
print(W / 'verification.json')
