"""Read-only site-plan authentication. No Lean, overlay, copy or Git mutation.

Writes only cache-plan.json in this new planning directory. Later provider
leads are explicitly separate from the selected first-leaf import closure.
"""
from pathlib import Path
import copy
import hashlib
import json
import re
import shutil

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
REV = D / 'reviews'
BB = R / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
HERE = Path(__file__).resolve().parent
pins = {}
observations = 0


def rec(p):
    p = Path(p)
    if not p.is_absolute():
        p = R / p
    b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))


def check(x):
    global observations
    a = rec(x['path'])
    assert a['sha256'] == x['sha256'], (x, a)
    if 'bytes' in x:
        assert a['bytes'] == x['bytes'], (x, a)
    pins[a['path']] = a
    observations += 1
    return a


def load(p, sha):
    check(dict(path=str(p), sha256=sha))
    return json.loads(Path(p).read_text())


def imports(p):
    s = Path(p).read_text()
    out, i, depth = [], 0, 0
    while i < len(s):
        pair = s[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            while i < len(s) and s[i] != '\n': i += 1
        else: out.append(s[i]); i += 1
    assert depth == 0, p
    return list(dict.fromkeys(['Init'] + [n for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', ''.join(out), re.M)
        for n in line.split()]))


basep = D / 'research/c222-home215-plan-20261027/cache-plan.json'
base = load(basep, 'a13475a1cb749a81800a1f7773df53b90582a4bba37badb128058371ec8a8137')
for x in base['authenticated_pins']:
    check(x)
mods = {m['module']: copy.deepcopy(m) for m in base['modules']}
rootp = REV / 'arithmetic-home215-root-replay.json'
root = load(rootp, '066d1724208fedc4e42a9cb5abfd9526c956aa791a662adcd54f824f6a0a0aa4')
rootmf = REV / 'arithmetic-home215-root-replay/FILES.json'
for x in load(rootmf, 'd804931bf03f72e7aa24697ee498cdd80905fee86813488d2be5b58f3aa452d5'):
    check(x)
assert root['status'] == 'PASS' and root['provider'] == '/tmp/home215-root-gwo_lm6e/lib'
rootreceipt = check(rec(REV / 'arithmetic-home215-root.md'))
authorp = REV / 'arithmetic-home215-replay.json'
author = load(authorp, '8c1c7fe38b55129f57debee97130603d22d70f57e23388474c6e8c1dc49064bc')
for row in root['records']:
    if row['module'].endswith('Checks'):
        continue
    assert row['exit_code'] == 0
    for key in ['source', 'snapshot', 'object', 'log', 'timing']:
        check(row[key])
    old = next(x for x in author['final']['records'] if x['module'] == row['module'])
    for key in ['source', 'object', 'log']:
        check(old[key])
        assert old[key]['sha256'] == row[key]['sha256'], key
    mods[row['module']] = dict(module=row['module'], source=row['source'], objects=[row['object']],
        actual_imports=imports(row['source']['path']), parent=rec(rootp),
        provider='Accepted independent ROOT Home provider; author history retained.',
        historical_provenance=row, author_provenance=old)

peerp = REV / 'native-adaptive-current2011-peer-replay.json'
peer = load(peerp, '6661c2f42baa774e9e2844b23e4621ddff2dca161424be140c00c0b0d436db48')
peermf = REV / 'native-adaptive-current2011-peer-replay/FILES.json'
for x in load(peermf, 'd7c08b0bbc1138055879d9387e67a4d59b007af5b9553e66ce0833ad372d03ae'):
    check(x)
assert peer['status'] == 'PASS'
check(peer['inputs'])
native = json.loads(Path(peer['inputs']['path']).read_text())
nmods = {m['module']: m for m in native['selected_custom']}
native_root_receipt = check(rec(REV / 'native-adaptive-current2011-root.md'))
native_root_mf = REV / 'native-adaptive-current2011-root-auth/FILES.json'
for x in load(native_root_mf, '0b908bbdc6b0e1562e095ec439c60b6b515c720fa262d190d17f2c687521ff04'):
    check(x)

direct = ['DiophantineConsistency.ArithmeticHome215', 'BusyBeaver.ZFC.KSites215']
boundary = {m['module']: copy.deepcopy(m) for m in base['external']}
order, seen, active, used, added, overlaps = [], set(), set(), set(), [], []


def visit(n):
    if n in seen:
        return
    if n not in mods and n in nmods:
        m = nmods[n]
        for key in ['source', 'object', 'original_object']:
            check(m[key])
        mods[n] = dict(module=n, source=m['source'], objects=[m['object']],
            actual_imports=m['actual_imports'], parent=rec(peerp),
            provider='Accepted NativeAdaptiveCurrent peer selected cache.', historical_provenance=m)
        added.append(n)
    if n not in mods:
        assert n in boundary, ('unknown import', n)
        used.add(n)
        return
    assert n not in active, ('cycle', n)
    active.add(n)
    m = mods[n]
    check(m['source'])
    assert imports(m['source']['path']) == m['actual_imports'], ('header mismatch', n)
    assert not m.get('refresh', False), n
    if n in nmods and n not in added:
        alt = nmods[n]
        for key in ['source', 'object', 'original_object']:
            check(alt[key])
        assert alt['source']['sha256'] == m['source']['sha256'], ('source overlap', n)
        overlaps.append(dict(module=n, selected_source=m['source'], selected_objects=m['objects'],
            alternate_source=alt['source'], alternate_object=alt['object'],
            primary_bytes_equal=m['objects'][0]['sha256'] == alt['object']['sha256'],
            selected_current_provider_retained=True))
    for child in m['actual_imports']:
        visit(child)
    for obj in m['objects']:
        check(obj)
    active.remove(n)
    seen.add(n)
    order.append(n)


for n in direct:
    visit(n)
assert set(mods) == seen
assert len(added) == 19
external = [boundary[n] for n in sorted(used)]
providers = []
for n in order:
    for obj in mods[n]['objects']:
        providers.append(dict(module=n, provider=check(obj), kind='selected cached artifact'))
for m in external:
    if 'source' in m:
        check(m['source'])
    for obj in [m['object'], *m['companion_observations']]:
        check(obj)
        suffix = ''.join(Path(obj['path']).suffixes)
        rel = Path(*m['module'].split('.')).with_suffix(suffix)
        first = next((Path(p)/rel for p in base['package_paths'] if (Path(p)/rel).is_file()), None)
        assert first is not None and rec(first)['sha256'] == obj['sha256'], (m['module'], obj)
        providers.append(dict(module=m['module'], provider=check(rec(first)), kind='actual first package artifact'))
assert not any(p.endswith('/Proofs/.lake/build/lib/lean') for p in base['package_paths'])

# These accepted records are later-route leads, not first-leaf imports.
later = []
for stem, sha in [
    ('arithmetic-control215-table-peer-replay.json', None),
    ('arithmetic-control-bisim-perm215-root-replay.json', '4dac153721bc15d83f4436031a6fa32ed9a8bdfacc384692ce29af969f8eea29'),
    ('arithmetic-dag-runtimeperm222-root-replay.json', 'ffb22a20778f060dbb4fe5f2440ee4d7e6509882878f0e8ce501f13810f83526')]:
    path = REV / stem
    packet = load(path, sha or rec(path)['sha256'])
    assert packet['status'] == 'PASS'
    rows = []
    for row in packet['records']:
        if row['module'].endswith('Checks'):
            continue
        assert row['exit_code'] == 0
        for key in ['source', 'object']:
            check(row[key])
        rows.append(dict(module=row['module'], source=row['source'], object=row['object']))
    later.append(dict(packet=rec(path), provider=packet['private_provider'], records=rows,
        scope='Existing later-route provider lead; no future union or refresh authorized here.'))
route_names = ['ControlCatalogue', 'ArithmeticControlTable', 'ArithmeticControlFile',
    'Permutation252Frame', 'ArithmeticPositiveSimulation254', 'KBoot215',
    'ArithmeticDispatchRebaseRotation240', 'ArithmeticSiteValuesRotation240',
    'ArithmeticControlSimulationRotation240', 'ArithmeticControlFrameDataRotation240',
    'ArithmeticSiteRotation240', 'ArithmeticSitePerm252']
route_sources = [check(rec(BB / (n+'.lean'))) for n in route_names]
site_text = (BB/'KSites215.lean').read_text()
blocks = [int(x) for x in re.findall(r'\bblock_(\d+)\b', site_text)]
assert sorted(blocks) == list(range(105))
batch_modules = [n for n in order if n.startswith('BusyBeaver.ZFC.KSites215Batch')]
assert len(batch_modules) == 9
finite_scope = dict(closed_certificate='KSites215.all_sites', distinct_blocks=105,
    block_occurrences=blocks, batch_modules=batch_modules,
    qualification='Text coverage cross-check only; accepted kernel all_sites and table/catalogue equality supply proof.')

counts = dict(cached_custom=len(order), Foundation=sum(n.startswith('Foundation.') for n in order),
    cached_artifacts=sum(len(mods[n]['objects']) for n in order), boundary_primaries=len(external),
    boundary_companions=sum(len(m['companion_observations']) for m in external),
    selected_first_artifact_providers=len(providers), refresh=0, proposed_new_leaves=2)
assert counts == dict(cached_custom=173, Foundation=95, cached_artifacts=458, boundary_primaries=41,
    boundary_companions=123, selected_first_artifact_providers=622, refresh=0, proposed_new_leaves=2), counts
for x in [base['compiler'], rec(HERE/'PROPOSAL.md'), rec(__file__)]:
    check(x)
for x in list(pins.values()):
    check(x)
free = shutil.disk_usage('/tmp').free
assert free >= 512*1024**2, free
result = dict(status='READ_ONLY_NO_LEAN_OVERLAY_OR_REFRESH', direct_imports=direct, counts=counts,
    modules=[mods[n] for n in order], topological_order=order, external=external,
    first_providers=providers, package_paths=base['package_paths'], compiler=base['compiler'],
    base=rec(basep), accepted_home_root=rec(rootp), accepted_home_manifest=rec(rootmf),
    accepted_home_receipt=rootreceipt, retained_home_author=rec(authorp),
    native_cache_peer=rec(peerp), native_cache_manifest=rec(peermf), native_inputs=peer['inputs'],
    native_root_receipt=native_root_receipt, native_root_manifest=rec(native_root_mf),
    added_cached_modules=added, source_identical_overlap_observations=overlaps,
    finite_site_scope=finite_scope, later_provider_leads_not_imports=later,
    later_or_guide_source_pins_not_imports=route_sources, proposal=rec(HERE/'PROPOSAL.md'),
    planner=rec(__file__), authenticated_pins=list(pins.values()), observations=observations,
    free_bytes_observed=free, reserve_bytes=512*1024**2,
    qualification='Only a read-only plan. Home accepted ROOT selected directly. No future canonical/control union approved.')
out = HERE/'cache-plan.json'
out.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(dict(counts=counts, added=added, unequal_overlaps=[x['module'] for x in overlaps if not x['primary_bytes_equal']],
    observations=observations, unique_paths=len(pins), plan=rec(out)), indent=2))
