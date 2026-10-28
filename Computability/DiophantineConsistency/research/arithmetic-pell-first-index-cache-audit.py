"""Read-only provider audit for the proposed internal first-index checkpoint.

No compiler, subprocess, overlay, dependency refresh, or proof-source edit.
Existing accepted plans and provider evidence remain unchanged.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
OUT = D / 'research/arithmetic-pell-first-index-cache-plan.json'
pins = {}
observations = 0


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def record(path):
    path = Path(path)
    data = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def check(pin):
    global observations
    actual = record(pin['path'])
    require(actual['sha256'] == pin['sha256'], 'hash: ' + pin['path'])
    if 'bytes' in pin:
        require(actual['bytes'] == pin['bytes'], 'size: ' + pin['path'])
    pins[actual['path']] = actual
    observations += 1
    return actual


def imports(path):
    source = Path(path).read_text()
    out = []
    i = depth = 0
    while i < len(source):
        pair = source[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if source[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            i += 2
        elif pair == '--':
            while i < len(source) and source[i] != '\n':
                i += 1
        else:
            out.append(source[i])
            i += 1
    require(depth == 0, 'comment balance')
    clean = ''.join(out)
    initial = [] if re.search(r'^\s*prelude\s*$', clean, re.M) else ['Init']
    return list(dict.fromkeys(initial + [name for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', clean, re.M)
        for name in line.split()]))


def load_pinned(relative, sha):
    pin = check(dict(path=str(D / relative), sha256=sha))
    return pin, json.loads(Path(pin['path']).read_text())


def manifest(relative, sha):
    pin, items = load_pinned(relative, sha)
    for item in items:
        check(dict(item, path=str(ROOT / item['path'])))
    return pin


def accepted(relative, sha, mf, mf_sha, module, provenance):
    packet_pin, packet = load_pinned(relative, sha)
    mf_pin = manifest(mf, mf_sha)
    require(packet['status'] == 'PASS', 'accepted status')
    for row in packet['records']:
        require(row['exit_code'] == 0, 'accepted command exit')
        for key in ['source', 'snapshot', 'object', 'log', 'timing']:
            check(row[key])
    for key in ['driver', 'state', 'durable_state', 'final_authentication',
                'inputs', 'providers', 'author_packet', 'author_manifest']:
        if key in packet:
            check(packet[key])
    row = next(row for row in packet['records'] if row['module'] == module)
    return dict(module=module, source=check(row['source']), objects=[check(row['object'])],
        imports=imports(row['source']['path']), supplement_packet=packet_pin,
        supplement_manifest=mf_pin, provenance=provenance)


require(not OUT.exists(), 'refuse overwrite')
parent_pin, parent = load_pinned('research/arithmetic-pell-half-index-cache-plan.json',
    'd208392a2a3b6c4f32d2525b242c13adc588d3af9fce2e5579a4476bf883ad1b')
first_pin, first = load_pinned('research/arithmetic-pell-first-norm-cache-plan.json',
    '36f362df517bfdd4d3ba06176005ce2d85e7b2591700b18a67a85fc69f009c66')
for plan in [parent, first]:
    for pin in plan['pins']:
        check(pin)
require(parent['compiler'] == first['compiler'], 'same compiler')
require(parent['boundary_search'] == first['boundary_search'], 'same boundary search')
mods = {entry['module']: entry for entry in parent['modules']}
external = {entry['module']: entry for entry in parent['external']}
overlaps = []
for entry in first['modules']:
    name = entry['module']
    require(name in mods, 'FirstNorm dependency unexpectedly absent from HalfIndex closure: ' + name)
    old = mods[name]
    require(check(old['source']) == check(entry['source']) and old['imports'] == entry['imports'],
            'overlap current source/header: ' + name)
    require([(x['sha256'], x['bytes']) for x in old['objects']] ==
            [(x['sha256'], x['bytes']) for x in entry['objects']], 'overlap object: ' + name)
    overlaps.append(name)
for entry in first['external']:
    require(external.get(entry['module']) == entry, 'same external boundary: ' + entry['module'])
for entry in [accepted('reviews/arithmetic-pell-half-index-root-replay.json',
    'de4ed3e2e9c519044c8a248fe38cd62cba19e541c4263b10c71e104aa0034890',
    'reviews/arithmetic-pell-half-index-root-replay/FILES.json',
    '4a62cbeaacdb1bb8472e1929e2bf3880771fc5996e875331cc784c537fdbcaa9',
    'DiophantineConsistency.ArithmeticPellHalfIndex',
    'Independently accepted ROOT HalfIndex main provider; Checks are evidence, not an import.'),
    accepted('reviews/arithmetic-pell-first-norm-peer-replay.json',
    '56ac5af7354876ddba346e91dc8c1f7d6e028bdd822bd13fb690dd48f288dff6',
    'reviews/arithmetic-pell-first-norm-peer-replay/FILES.json',
    '3f3acf4b1ccf75e7facd4fcbedd6072cdb8571174de37ce1e89796dd8ed89706',
    'DiophantineConsistency.ArithmeticPellFirstNorm',
    'Independent peer provider accepted by ROOT (ad92d07c8a); ROOT did not run a third compiler.')]:
    require(entry['module'] not in mods, 'new accepted main')
    mods[entry['module']] = entry
first_root_mf = manifest('reviews/arithmetic-pell-first-norm-root-auth/FILES.json',
    '52c89d4c12e8721203f9e80f52af2c8ed7fcc832fb7df19dabdf7953843b3776')
first_root_receipt = check(dict(path=str(D / 'reviews/arithmetic-pell-first-norm-root.md'),
    sha256='d1a90b7e861b222252aed738180802afa0a0f68239db1d1bf3ab4d69dc6fc34c'))
direct = ['DiophantineConsistency.ArithmeticPellHalfIndex',
          'DiophantineConsistency.ArithmeticPellFirstNorm']
seen, active, used, order = set(), set(), set(), []


def visit(name):
    if name not in mods:
        require(name in external, 'unknown boundary: ' + name)
        used.add(name)
        return
    if name in seen:
        return
    require(name not in active, 'cycle')
    active.add(name)
    item = mods[name]
    check(item['source'])
    require(imports(item['source']['path']) == item['imports'], 'current header: ' + name)
    for dep in item['imports']:
        visit(dep)
    for obj in item['objects']:
        check(obj)
    active.remove(name)
    seen.add(name)
    order.append(name)


for name in direct:
    visit(name)
require(seen == set(mods) and used == set(external), 'exact reachable closure')
boundary = [external[name] for name in sorted(used)]
providers, virtual = [], {}
for name in order:
    for obj in mods[name]['objects']:
        relative = str(Path(*name.split('.')[:-1]) / Path(obj['path']).name)
        require(relative not in virtual, 'prospective provider collision')
        virtual[relative] = obj
        providers.append(dict(module=name, relative=relative, expected=obj, actual=check(obj),
            kind='Prospective private link; no overlay created'))
for item in boundary:
    check(item['source'])
    for obj in item['artifacts']:
        check(obj)
        relative = str(Path(*item['module'].split('.')[:-1]) / Path(obj['path']).name)
        require(relative not in virtual, 'boundary shadowing')
        provider = next((Path(root) / relative for root in parent['boundary_search']
                         if (Path(root) / relative).is_file()), None)
        require(provider is not None, 'missing actual boundary provider')
        providers.append(dict(module=item['module'], relative=relative, expected=obj,
            actual=check(dict(obj, path=str(provider))), kind='Actual explicit boundary first provider'))
counts = dict(custom=len(order), Foundation=sum(x.startswith('Foundation.') for x in order),
    artifacts=len(virtual), external=len(boundary), boundary_artifacts=len(providers)-len(virtual),
    boundary_primaries=len(boundary), boundary_companions=len(providers)-len(virtual)-len(boundary),
    actual_first_providers=len(providers), fresh_prerequisites=0)
require(counts == dict(custom=108, Foundation=95, artifacts=393, external=38,
    boundary_artifacts=114, boundary_primaries=38, boundary_companions=76,
    actual_first_providers=507, fresh_prerequisites=0), 'exact proposed scope')
refs = []
for name in ['Carrier65', 'Carrier65Witness', 'CarrierRankBounds', 'CurrentMaskData2011',
    'CurrentKernelData2011', 'CurrentCarrierArithmetic2011', 'CurrentPolynomialWindow2011',
    'NativePellBootstrap', 'NativePellFirstIndex', 'NativePellStepDown']:
    refs.append(check(record(D / ('Lean/DiophantineConsistency/' + name + '.lean'))))
check(parent['compiler'])
check(record(__file__))
for pin in list(pins.values()):
    check(pin)
result = dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',
    parents=[parent_pin, first_pin], first_norm_root_manifest=first_root_mf,
    first_norm_root_receipt=first_root_receipt, identical_overlaps=overlaps,
    direct_imports=direct, counts=counts, modules=[mods[name] for name in order],
    topological_order=order, external=boundary, boundary_search=parent['boundary_search'],
    compiler=parent['compiler'], artifact_providers=providers, references_only=refs,
    audit=record(__file__), pins=list(pins.values()), observations=observations,
    unique_paths=len(pins), scope='Proposed ArithmeticPellFirstIndex + Checks only. Actual first '
    'and main norms, first carrier and scalar windows derive both indices and omitted positive '
    'quotient; prospective literal scalar client derives windows from actual transport/port '
    'inequalities. No compiler, overlay, refresh or proof-source edits. No assumed source, '
    'classification/index, large-ordinate or half-window oracle; no power/cofinal/PA/HA claim. '
    'All prior package provenance qualifications are inherited; current pins do not claim '
    'fresh dependency compilation. The old FirstNorm external_companions=114 field means '
    '38 boundary primaries plus76 companions, not114 companions.')
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(plan=record(OUT), counts=counts, observations=observations,
                     unique_paths=len(pins)), indent=2))
