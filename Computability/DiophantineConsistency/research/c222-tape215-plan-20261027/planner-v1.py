"""Read-only source/object audit; writes only this new planning packet.

No compiler, overlay, symlink, cache mutation, or existing-source write.
The source-level proposal must be approved separately before implementation.
"""
from pathlib import Path
import copy
import hashlib
import json
import re
import subprocess

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
HERE = Path(__file__).resolve().parent
BB = R / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
DC = D / 'Lean/DiophantineConsistency'
pins = {}
observations = 0


def record(path):
    p = Path(path)
    return {'path': str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
            'bytes': p.stat().st_size}


def check(r):
    global observations
    a = record(r['path'])
    assert a['sha256'] == r['sha256'], (r, a)
    pins[a['path']] = a
    observations += 1
    return a


def load(path, expected=None):
    r = record(path)
    if expected is not None:
        assert r['sha256'] == expected, (r, expected)
    check(r)
    return json.loads(Path(path).read_text())


def imports(path):
    s = Path(path).read_text()
    out, i, depth = [], 0, 0
    while i < len(s):
        p = s[i:i+2]
        if depth:
            if p == '/-': depth += 1; i += 2
            elif p == '-/': depth -= 1; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif p == '/-': depth = 1; i += 2
        elif p == '--':
            while i < len(s) and s[i] != '\n': i += 1
        else: out.append(s[i]); i += 1
    assert depth == 0
    return list(dict.fromkeys(['Init'] + [name for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', ''.join(out), re.M)
        for name in line.split()]))


deps_path = REV / 'arithmetic-machine215-replay/dependencies-current.json'
deps = load(deps_path, '722d7de74e83cdcaad54f433973cead57051dc855ee3c0841815380351930fa7')
final_path = REV / 'arithmetic-machine215-replay/final.json'
final = load(final_path, '0c8b1f3057fea9887a9273a56d3234dd97b69a36305f4dd8541405cef5a7d27d')
machine_root_path = REV / 'arithmetic-machine215-root-replay/ROOT.json'
machine_root = load(machine_root_path)
assert machine_root['status'] == final['status'] == 'PASS'
seven_path = REV / 'arithmetic-machine215-root-replay/fresh-seven.json'
seven = load(seven_path, '55aa8a69219b0c43fd1fc13c6018026b472f53fd40d74e30a4ff69b5099b5034')
native_path = REV / 'native-adaptive-current2011-peer-replay/INPUTS.json'
native = load(native_path)
runtime_path = D / 'research/c222-dag-runtimeperm222-cache-plan-20261027.json'
runtime = load(runtime_path, 'e0d0736f57ebddca9a2530f93fdec69308ed77c1dec74c18787866f2ebfaf3d6')
for p in [REV / 'arithmetic-machine215-root.md', REV / 'arithmetic-machine215-author.md',
          REV / 'native-adaptive-current2011-peer.md']:
    check(record(p))

mods = {}
for m in deps['modules']:
    mods[m['module']] = {'module': m['module'],
        'source': {'path': m['source'], 'sha256': m['source_sha256']},
        'actual_imports': m['imports'], 'objects': copy.deepcopy(m['objects']),
        'parent': record(deps_path), 'historical_provenance': copy.deepcopy(m)}
for m in final['fresh']:
    if m['module'].endswith('Checks'): continue
    n = m['module']
    selected = {'path': m['object'], 'sha256': m['object_sha256']}
    provider = 'Accepted author object; independent ROOT replay is byte-identical.'
    q = next((x for x in seven if n == 'DiophantineConsistency.' + x['module']), None)
    if q is not None:
        assert q['exit_code'] == 0 and q['source_sha256'] == m['source_sha256']
        selected = {'path': q['command'][q['command'].index('-o')+1],
                    'sha256': q['object_sha256']}
        assert selected['sha256'] == m['object_sha256']
        provider = 'Accepted independent ROOT fresh primary (fresh-seven.json).'
        check({'path': q['log'], 'sha256': q['log_sha256']})
    assert m['exit_code'] == 0
    check(m['state'])
    mods[n] = {'module': n,
        'source': {'path': m['source'], 'sha256': m['source_sha256']},
        'actual_imports': imports(m['source']), 'objects': [selected],
        'parent': record(final_path), 'root_parent': record(machine_root_path),
        'provider': provider, 'original_author_object':
        {'path': m['object'], 'sha256': m['object_sha256']}}

overlaps = []
for m in native['selected_custom']:
    n = m['module']
    if n in mods:
        assert mods[n]['source']['sha256'] == m['source']['sha256'], n
        overlaps.append({'module': n, 'same_source': True,
                         'selected_primary': mods[n]['objects'][0],
                         'alternate_accepted_primary': m['object']})
    else:
        mods[n] = {'module': n, 'source': m['source'],
            'actual_imports': m['actual_imports'], 'objects': [m['object']],
            'parent': record(native_path), 'historical_provenance': m}

bound = {}
for x in final['external_boundary']:
    bound[x['module']] = {'module': x['module'], 'source': x['observed_source'],
        'object': x['object'], 'companion_observations': x['companions'],
        'parent': record(final_path)}
for x in native['external_boundary']:
    bound[x['module']] = {'module': x['module'], 'source': x['source'],
        'object': x['artifacts'][0], 'companion_observations': x['artifacts'][1:],
        'parent': record(native_path)}
for x in runtime['external']:
    old = bound.get(x['module'], {})
    obj = {k: x[k] for k in ['path', 'sha256']}
    if 'object' in old: assert old['object']['sha256'] == obj['sha256']
    bound[x['module']] = {'module': x['module'], 'object': obj,
        'companion_observations': x['companion_observations'],
        'parent': record(runtime_path), **({'source': old['source']} if 'source' in old else {})}

direct = ['DiophantineConsistency.ArithmeticMachineRun215',
          'BusyBeaver.ZFC.KBoot215',
          'Foundation.FirstOrder.Arithmetic.Definability.Absoluteness']
order, seen, active, used = [], set(), set(), set()


def visit(n):
    if n not in mods:
        assert n in bound, ('unknown boundary', n)
        used.add(n)
        return
    if n in seen: return
    assert n not in active, ('cycle', n)
    active.add(n)
    m = mods[n]
    m['source'] = check(m['source'])
    actual = imports(m['source']['path'])
    assert actual == m['actual_imports'], ('header', n, actual, m['actual_imports'])
    for dep in actual: visit(dep)
    for obj in m['objects']: check(obj)
    active.remove(n)
    seen.add(n)
    order.append(n)


for n in direct: visit(n)
external = [bound[n] for n in sorted(used)]
for x in external:
    if 'source' in x: check(x['source'])
    check(x['object'])
    for r in x['companion_observations']: check(r)
    rel = Path(*x['module'].split('.')).with_suffix('.olean')
    first = next((Path(p)/rel for p in runtime['package_paths'] if (Path(p)/rel).exists()), None)
    assert first is not None and record(first)['sha256'] == x['object']['sha256'], x['module']
    x['actual_first_provider'] = check(record(first))

control_parents = []
for name, sha in [
    ('arithmetic-dag-runtimeperm222-root-replay.json', 'ffb22a20778f060dbb4fe5f2440ee4d7e6509882878f0e8ce501f13810f83526'),
    ('arithmetic-control-bisim-perm215-root-replay.json', '4dac153721bc15d83f4436031a6fa32ed9a8bdfacc384692ce29af969f8eea29')]:
    load(REV/name, sha)
    control_parents.append(record(REV/name))
for stem in ['KBoot215','KBoot','KSim','KRuntimeCore','KTape','KHomeReady',
             'ArithmeticMachineRunFromPerm252','ArithmeticBootstrapPerm252',
             'ArithmeticTapePrefix254','ArithmeticMachineUniformScansPerm252',
             'ArithmeticSymbolicTapePerm252','ArithmeticSitePerm252',
             'ArithmeticControlFrame254','ArithmeticControlSimulation254']:
    check(record(BB/(stem+'.lean')))
check(record(__file__))
check(deps['compiler'])
for r in list(pins.values()): check(r)
selected = [mods[n] for n in order]
counts = {'custom': len(selected), 'Foundation': sum(n.startswith('Foundation.') for n in seen),
          'cached_artifacts': sum(len(m['objects']) for m in selected),
          'boundary': len(used),
          'boundary_companions': sum(len(x['companion_observations']) for x in external),
          'refresh': 0, 'proposed_fresh_leaves': 2}
result = {'status': 'READ_ONLY_PLAN_NO_COMPILE_OR_OVERLAY',
    'snapshot': subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
    'scope': 'Actual decimal run from arbitrary tape codes, sparse-label one-step binding, exact boot and arbitrary internal continuations. No site/runtime calibration or HA endpoint.',
    'direct_imports': direct, 'counts': counts, 'modules': selected,
    'topological_order': order, 'external': external,
    'package_paths': runtime['package_paths'], 'compiler': deps['compiler'],
    'parents': [record(p) for p in [deps_path,final_path,machine_root_path,seven_path,native_path,runtime_path]],
    'accepted_control_parents_not_proposed_imports': control_parents,
    'agreeing_source_overlaps': [x for x in overlaps if x['module'] in seen],
    'authenticated_pins': list(pins.values()), 'observations': observations,
    'planner': record(__file__),
    'source_scope': 'Current header DAG and all selected cache bytes rechecked. No new compilation. Existing arithmetic215 and KBoot objects reused only at unchanged source pins; package boundary explicit.'}
out = HERE/'cache-plan.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'counts':counts,'plan':record(out),'pins':len(pins),'observations':observations},indent=2))
