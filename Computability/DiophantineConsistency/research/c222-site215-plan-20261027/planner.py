"""Read-only planning audit. Writes only this new packet's cache-plan.json.

No compiler, overlay, symlink, prerequisite copy, Lean edit or Git mutation.
The historical prefix object is pinned but deliberately never selected.
"""
from pathlib import Path
import copy
import hashlib
import json
import re
import shutil
import subprocess

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
BB = R / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
HERE = Path(__file__).resolve().parent
pins, observations = {}, 0


def record(path):
    p = Path(path)
    if not p.is_absolute():
        p = R / p
    return {'path': str(p), 'sha256': hashlib.sha256(p.read_bytes()).hexdigest(),
            'bytes': p.stat().st_size}


def check(r):
    global observations
    a = record(r['path'])
    assert a['sha256'] == r['sha256'], (r, a)
    pins[a['path']] = a
    observations += 1
    return a


def load(path, expected):
    r = record(path)
    assert r['sha256'] == expected, (r, expected)
    check(r)
    return json.loads(Path(r['path']).read_text())


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
    return list(dict.fromkeys(['Init'] + [n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', ''.join(out), re.M)
        for n in line.split()]))


base_path = D / 'research/c222-tape215-plan-20261027/cache-plan.json'
base = load(base_path, 'b03ba7a4b432b6e03f79f59aacdf5cf2971f900e0391a13b47a6be31fab934ec')
for r in base['authenticated_pins']:
    check(r)
root_path = REV / 'arithmetic-machine-tape215-root-replay.json'
root = load(root_path, 'b234385f98543b84ab13015483f0025be9ce58b102b5d936a8fabbf88d1b4fc9')
root_manifest_path = REV / 'arithmetic-machine-tape215-root-replay/FILES.json'
root_manifest = load(root_manifest_path, 'f49e05f14d4de0c1147f77dcc292c3bd6677b3b61faae774d9308e23671b2fd9')
for r in root_manifest:
    check(r)
assert root['status'] == 'PASS' and root['private_provider'] == '/tmp/machine-tape215-root-bbarbz31/lib'
check(record(REV / 'arithmetic-machine-tape215-root.md'))
mods = {m['module']: copy.deepcopy(m) for m in base['modules']}
rec = next(r for r in root['records'] if r['module'] == 'DiophantineConsistency.ArithmeticMachineTape215')
assert rec['exit_code'] == 0 and rec['author_object_and_full_log_equal']
for key in ['source', 'snapshot', 'log', 'timing', 'object']:
    check(rec[key])
mods[rec['module']] = {
    'module': rec['module'], 'source': rec['source'],
    'actual_imports': imports(rec['source']['path']), 'objects': [rec['object']],
    'parent': record(root_path), 'provider': 'Accepted independent ROOT pair, commit e28f94bba6.',
    'historical_provenance': rec}

historic_path = Path('/tmp/zfc-tape-prefix/run1/verification.json')
historic = load(historic_path, 'd6bc62b014b1c1bd4d197b7f2c7a5f53c2393002c9ce82543e1ebf81fc118562')
assert historic['status'] == 'PASS'
prefix_source = check({'path': str(BB / 'ArithmeticTapePrefix254.lean'),
    'sha256': '396b573e4e94058859608ffa74be668f1d29a092f4853bdeafc0702da222cd55'})
check(historic['source'])
check({'path': historic['source']['snapshot'], 'sha256': prefix_source['sha256']})
check(historic['module_object'])
check(historic['compiler'])
assert all(c['exit_code'] == 0 for c in historic['commands'])
assert historic['compiler']['sha256'] == base['compiler']['sha256']
overlaps = []
for m in historic['reused_modules']:
    n = m['module']
    current = mods[n]['source']
    check(current)
    overlaps.append({'module': n, 'historical_source':
        {'path': m['source'], 'sha256': m['source_sha256']},
        'selected_current_source': current,
        'source_matches': m['source_sha256'] == current['sha256']})
assert len(overlaps) == 11 and sum(not m['source_matches'] for m in overlaps) == 9
prefix = 'BusyBeaver.ZFC.ArithmeticTapePrefix254'
mods[prefix] = {'module': prefix, 'source': prefix_source,
    'actual_imports': imports(prefix_source['path']), 'objects': [],
    'refresh': True, 'refresh_reason': 'Unchanged numeric helper; nine historical custom dependencies differ. Historical object is not selected.',
    'historical_record': record(historic_path), 'historical_object_not_selected': historic['module_object']}
direct = ['DiophantineConsistency.ArithmeticMachineTape215', prefix]
bound = {x['module']: copy.deepcopy(x) for x in base['external']}
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
    check(m['source'])
    actual = imports(m['source']['path'])
    assert actual == m['actual_imports'], ('header', n, actual, m['actual_imports'])
    for dep in actual: visit(dep)
    for obj in m['objects']: check(obj)
    active.remove(n)
    seen.add(n)
    order.append(n)


for n in direct: visit(n)
external = [bound[n] for n in sorted(used)]
first_providers = []
for n in order:
    for obj in mods[n]['objects']:
        first_providers.append({'module': n, 'provider': check(obj),
            'kind': 'selected private/cache artifact; future overlay link, not created here'})
for x in external:
    if 'source' in x: check(x['source'])
    for obj in [x['object']] + x['companion_observations']:
        check(obj)
        suffix = ''.join(Path(obj['path']).suffixes)
        relative = Path(*x['module'].split('.')).with_suffix(suffix)
        first = next((Path(p)/relative for p in base['package_paths'] if (Path(p)/relative).exists()), None)
        assert first is not None and record(first)['sha256'] == obj['sha256'], (x['module'], obj)
        first_providers.append({'module': x['module'], 'provider': check(record(first)),
            'kind': 'actual first package/stdlib path'})

# Later route source and accepted data-provider leads. They are not imports
# of the first proposed pair, and are not added to its selected-provider count.
route_stems = ['KTape', 'KRuntimeCore', 'KHome', 'KHomeReady', 'KSim', 'KSites215',
    'KBoot215', 'KSource215Program', 'ControlCatalogue', 'Permutation252Frame',
    'ArithmeticControlFile', 'ArithmeticControlTable', 'ArithmeticControl215Table',
    'ArithmeticControlBisimPerm215', 'ArithmeticDagRuntimePerm222',
    'ArithmeticPositiveSimulation254', 'ArithmeticMachineUniformScansPerm252',
    'ArithmeticSymbolicTapePerm252', 'ArithmeticSymbolicBoxesPerm252',
    'ArithmeticSymbolicExecutionPerm252', 'ArithmeticSitePerm252',
    'ArithmeticControlFrame254', 'ArithmeticControlRun254']
route_sources = [check(record(BB/(s+'.lean'))) for s in route_stems]
route_sources += [check(record(p)) for p in sorted(BB.glob('KSites215Batch*.lean'))]
native_path = REV / 'native-adaptive-current2011-peer-replay/INPUTS.json'
native = json.loads(native_path.read_text())
check(record(native_path))
native_mods = {m['module']: m for m in native['selected_custom']}
later_data = []
for n in ['BusyBeaver.ZFC.KSim', 'BusyBeaver.ZFC.KHomeReady', 'BusyBeaver.ZFC.KSites215'] + [
        'BusyBeaver.ZFC.' + p.stem for p in sorted(BB.glob('KSites215Batch*.lean'))]:
    m = native_mods[n]
    check(m['source']); check(m['object'])
    assert imports(m['source']['path']) == m['actual_imports']
    later_data.append({'module': n, 'source': m['source'], 'object': m['object'],
                       'parent': record(native_path), 'scope': 'Later data-provider lead; not selected first-leaf import.'})
route_packets = []
for stem, expected in [
    ('arithmetic-control215-table-peer-replay.json', None),
    ('arithmetic-control-bisim-perm215-root-replay.json', '4dac153721bc15d83f4436031a6fa32ed9a8bdfacc384692ce29af969f8eea29'),
    ('arithmetic-dag-runtimeperm222-root-replay.json', 'ffb22a20778f060dbb4fe5f2440ee4d7e6509882878f0e8ce501f13810f83526')]:
    path = REV/stem
    d = load(path, expected or record(path)['sha256'])
    assert d['status'] == 'PASS'
    entries = []
    for r in d['records']:
        if r['module'].endswith('Checks'): continue
        assert r['exit_code'] == 0
        check(r['source']); check(r['object'])
        entries.append({'module': r['module'], 'source': r['source'], 'object': r['object']})
    route_packets.append({'packet': record(path), 'records': entries,
                          'scope': 'Accepted later route only; not selected first-leaf imports.'})

check(record(HERE/'PROPOSAL.md'))
check(record(__file__))
check(base['compiler'])
for r in list(pins.values()): check(r)
selected = [mods[n] for n in order]
counts = {'custom_total': len(selected), 'cached_custom': sum(not m.get('refresh', False) for m in selected),
    'Foundation': sum(n.startswith('Foundation.') for n in seen),
    'cached_artifacts': sum(len(m['objects']) for m in selected), 'boundary_primaries': len(used),
    'boundary_companions': sum(len(x['companion_observations']) for x in external),
    'selected_first_artifact_providers': len(first_providers),
    'proposed_unchanged_refresh': 1, 'proposed_new_leaves': 2}
assert counts == {'custom_total':147,'cached_custom':146,'Foundation':95,
    'cached_artifacts':431,'boundary_primaries':41,'boundary_companions':123,
    'selected_first_artifact_providers':595,'proposed_unchanged_refresh':1,'proposed_new_leaves':2}, counts
free = shutil.disk_usage('/tmp').free
assert free >= 512*1024*1024, free
result = {'status': 'READ_ONLY_PROPOSAL_NO_COMPILER_OR_OVERLAY',
    'snapshot': subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
    'scope': 'Actual215 scans and all four register-box executions; later site/control route remains separate.',
    'direct_imports': direct, 'counts': counts, 'modules': selected, 'topological_order': order,
    'external': external, 'package_paths': base['package_paths'], 'first_providers': first_providers,
    'compiler': base['compiler'], 'accepted_tape_root': record(root_path),
    'accepted_tape_manifest': record(root_manifest_path), 'base': record(base_path),
    'historical_prefix': {'record': record(historic_path), 'source': prefix_source,
        'historical_object_not_selected': historic['module_object'], 'overlap_audit': overlaps,
        'historical_commands': historic['commands']},
    'later_route_source_pins': route_sources, 'later_data_providers_not_first_imports': later_data,
    'later_control_packets_not_first_imports': route_packets,
    'authenticated_pins': list(pins.values()), 'observations': observations,
    'proposal': record(HERE/'PROPOSAL.md'), 'planner': record(__file__),
    'free_bytes_observed': free, 'reserve_bytes': 512*1024*1024,
    'qualification': 'Historical Prefix object is excluded. This plan authorizes no build; one unchanged helper refresh requires ROOT approval. No new Foundation, source mutation, or old252 semantic reuse.'}
out = HERE/'cache-plan.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'counts':counts,'plan':record(out),'pins':len(pins),'observations':observations},indent=2))
