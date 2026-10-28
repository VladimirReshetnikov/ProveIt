"""Read-only canonical-frame plan authentication; never invokes Lean or Git.

Writes only this new directory's cache-plan.json. No overlay is created.
All inherited inventories remain immutable and are referenced by hash.
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
    a = check(dict(path=str(p), sha256=sha))
    return json.loads(Path(a['path']).read_text())


def manifest(p, sha):
    rows = load(p, sha)
    assert isinstance(rows, list)
    for x in rows:
        check(x)  # All three selected manifests use repository-relative paths.
    return rec(p)


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


assert shutil.disk_usage('/tmp').free >= 512*1024**2
basep = D / 'research/c222-site-execution215-plan-20261027/cache-plan.json'
base = load(basep, 'a2475b3256c6bdaf2cdcc25aafc7394500ab0fcdd9ae4cfdd12568096306530b')
for x in base['authenticated_pins']:
    check(x)
mods = {m['module']: copy.deepcopy(m) for m in base['modules']}
base_names = set(mods)

sitep = REV / 'arithmetic-site215-root-replay.json'
site = load(sitep, 'ab7cff97ec8157b3987715bcd99b2155f7ff04b871e61965c6ec67e6200563ba')
sitemf = manifest(REV / 'arithmetic-site215-root-replay/FILES.json',
    'f08b5d950653001f31cb4532455f692630519e783e79b74e14a4e8973d746d94')
assert site['status'] == 'PASS' and site['provider'] == '/tmp/site215-root-1ub48_h4/lib'
site_receipt = check(rec(REV / 'arithmetic-site215-root.md'))
site_authorp = REV / 'arithmetic-site215-replay.json'
site_author = load(site_authorp, '7ec6e9bf58d44960bd1d60a0f364229ce7a6f31d85f749c3e1a45a0484acdad9')

tablep = REV / 'arithmetic-control215-table-peer-replay.json'
table = load(tablep, '6a39c93b890faceff9f1364b43bcc5e431f6ff6e9beb185913eb0797e07ab830')
tablemf = manifest(REV / 'arithmetic-control215-table-peer-replay/FILES.json',
    '86c7afe6d69844564d5e158414972bf3ebc70905a734cf4857f7900756e2cd55')
table_rootmf = manifest(REV / 'arithmetic-control215-table-root-auth/FILES.json',
    'e09c83c858e0bef4e35a7cbf73c6bca04cc8fc6ccd1e701aa9048b2375a68768')
table_receipt = check(rec(REV / 'arithmetic-control215-table-root.md'))
assert table['status'] == 'PASS' and table['private_provider'] == '/tmp/control215-table-peer-_nt2n9b9/lib'
ts = load(table['state']['path'], table['state']['sha256'])
ti = load(ts['inputs']['path'], ts['inputs']['sha256'])
for x in ti['pins']:
    check(x)
assert ti['compiler']['sha256'] == base['compiler']['sha256']
tablemods = {m['module']: m for m in ti['modules']}

# Keep the accepted Site route at each common module, comparing every
# inherited artifact (not merely the primary .olean) against the table route.
overlaps = []
added = []
for n, m in tablemods.items():
    check(m['source'])
    for o in m['objects']:
        check(o)
    if n in mods:
        a = mods[n]
        assert a['source']['sha256'] == m['source']['sha256'], ('source overlap', n)
        aa = {''.join(Path(o['path']).suffixes): o['sha256'] for o in a['objects']}
        bb = {''.join(Path(o['path']).suffixes): o['sha256'] for o in m['objects']}
        assert aa == bb, ('artifact overlap', n, aa, bb)
        overlaps.append(dict(module=n, selected_source=a['source'], selected_objects=a['objects'],
            alternate_source=m['source'], alternate_objects=m['objects'],
            all_artifact_bytes_equal=True))
    else:
        mods[n] = copy.deepcopy(m)
        mods[n]['parent_inventory'] = check(ts['inputs'])
        added.append(n)


def add_leaf(packet, packet_path, wanted, author_records=None):
    row = next(x for x in packet['records'] if x['module'] == wanted)
    assert row['exit_code'] == 0
    for key in ['source', 'snapshot', 'object', 'log', 'timing']:
        check(row[key])
    author = None
    if author_records is not None:
        author = next(x for x in author_records if x['module'] == wanted)
        for key in ['source', 'object', 'log']:
            check(author[key])
            assert author[key]['sha256'] == row[key]['sha256']
    assert wanted not in mods
    mods[wanted] = dict(module=wanted, source=row['source'], objects=[row['object']],
        actual_imports=imports(row['source']['path']), parent=rec(packet_path),
        provider='Accepted independent provider; historical records retained.',
        historical_provenance=row, author_provenance=author)


add_leaf(site, sitep, 'DiophantineConsistency.ArithmeticSite215', site_author['final']['records'])
add_leaf(table, tablep, 'BusyBeaver.ZFC.ArithmeticControl215Table')
direct = ['DiophantineConsistency.ArithmeticSite215', 'BusyBeaver.ZFC.ArithmeticControl215Table']
boundary = {m['module']: copy.deepcopy(m) for m in base['external']}
for x in ti['external']:
    assert x['module'] in boundary
    assert x['sha256'] == boundary[x['module']]['object']['sha256']

order, seen, active, used = [], set(), set(), set()


def visit(n):
    if n in seen:
        return
    if n not in mods:
        assert n in boundary, ('unknown boundary', n)
        used.add(n)
        return
    assert n not in active, ('import cycle', n)
    active.add(n)
    m = mods[n]
    check(m['source'])
    actual = imports(m['source']['path'])
    assert actual == m['actual_imports'], ('header mismatch', n)
    assert not m.get('refresh', False)
    for child in actual:
        visit(child)
    for o in m['objects']:
        check(o)
    active.remove(n)
    seen.add(n)
    order.append(n)


for n in direct:
    visit(n)
assert set(mods) == seen, ('unreachable modules', set(mods)-seen)
assert len(added) == 16
external = [boundary[n] for n in sorted(used)]
providers, relative_paths = [], set()
for n in order:
    for obj in mods[n]['objects']:
        suffix = ''.join(Path(obj['path']).suffixes)
        rel = str(Path(*n.split('.')).with_suffix(suffix))
        assert rel not in relative_paths, ('duplicate overlay artifact', rel)
        relative_paths.add(rel)
        providers.append(dict(module=n, relative_path=rel, provider=check(obj),
            kind='planned private cached artifact; no overlay created'))
for m in external:
    if 'source' in m:
        check(m['source'])
    for obj in [m['object'], *m['companion_observations']]:
        check(obj)
        suffix = ''.join(Path(obj['path']).suffixes)
        rel = Path(*m['module'].split('.')).with_suffix(suffix)
        assert str(rel) not in relative_paths
        relative_paths.add(str(rel))
        first = next((Path(p)/rel for p in base['package_paths'] if (Path(p)/rel).is_file()), None)
        assert first is not None and rec(first)['sha256'] == obj['sha256'], (m['module'], obj)
        providers.append(dict(module=m['module'], relative_path=str(rel), provider=check(rec(first)),
            kind='actual first package artifact'))
assert not any(p.endswith('/Proofs/.lake/build/lib/lean') for p in base['package_paths'])

guides = [check(rec(BB/(n+'.lean'))) for n in [
    'ControlTableBinding', 'ControlCatalogueRotation240',
    'ArithmeticControlFrameDataRotation240', 'ArithmeticDispatchRebaseRotation240',
    'ArithmeticSiteValuesRotation240', 'ArithmeticPositiveSimulation254']]
assert all(g['path'] not in [mods[n]['source']['path'] for n in order] for g in guides)
later = []
for stem, sha in [
    ('arithmetic-control-bisim-perm215-root-replay.json', '4dac153721bc15d83f4436031a6fa32ed9a8bdfacc384692ce29af969f8eea29'),
    ('arithmetic-dag-runtimeperm222-root-replay.json', 'ffb22a20778f060dbb4fe5f2440ee4d7e6509882878f0e8ce501f13810f83526')]:
    p = REV/stem
    j = load(p, sha)
    assert j['status'] == 'PASS'
    rows = []
    for row in j['records']:
        if row['module'].endswith('Checks'):
            continue
        rows.append(dict(module=row['module'], source=check(row['source']), object=check(row['object'])))
    later.append(dict(packet=rec(p), records=rows, scope='Later route only; not selected as new imports.'))

counts = dict(cached_custom=len(order), Foundation=sum(n.startswith('Foundation.') for n in order),
    cached_artifacts=sum(len(mods[n]['objects']) for n in order), boundary_primaries=len(external),
    boundary_companions=sum(len(m['companion_observations']) for m in external),
    selected_first_artifact_providers=len(providers), refresh=0, proposed_new_leaves=2)
assert counts == dict(cached_custom=191, Foundation=95, cached_artifacts=476,
    boundary_primaries=41, boundary_companions=123, selected_first_artifact_providers=640,
    refresh=0, proposed_new_leaves=2), counts
for x in [base['compiler'], rec(HERE/'PROPOSAL.md'), rec(__file__)]:
    check(x)
for x in list(pins.values()):
    check(x)
free = shutil.disk_usage('/tmp').free
assert free >= 512*1024**2, free
result = dict(status='READ_ONLY_NO_LEAN_OVERLAY_OR_REFRESH', direct_imports=direct, counts=counts,
    modules=[mods[n] for n in order], topological_order=order, external=external,
    first_providers=providers, package_paths=base['package_paths'], compiler=base['compiler'],
    base=rec(basep), accepted_site_root=rec(sitep), accepted_site_manifest=sitemf,
    accepted_site_receipt=site_receipt, retained_site_author=rec(site_authorp),
    accepted_table_peer=rec(tablep), accepted_table_peer_manifest=tablemf,
    accepted_table_root_manifest=table_rootmf, accepted_table_root_receipt=table_receipt,
    table_inputs=check(ts['inputs']), retained_table_provider_supplement=ti['provider_supplement'],
    added_cached_table_modules=added, overlap_observations=overlaps,
    inherited_unequal_kzip='Retained in base Site inventory; no alternate selected here.',
    guide_source_pins_not_imports=guides, later_route_leads_not_imports=later,
    proposal=rec(HERE/'PROPOSAL.md'), planner=rec(__file__), authenticated_pins=list(pins.values()),
    observations=observations, free_bytes_observed=free, reserve_bytes=512*1024**2,
    qualification='Read-only exact proposal; Site ROOT and table accepted peer selected directly. No launch performed.')
out = HERE/'cache-plan.json'
out.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(dict(counts=counts, added=added, observations=observations,
    unique_paths=len(pins), free_bytes=free, plan=rec(out)), indent=2))
