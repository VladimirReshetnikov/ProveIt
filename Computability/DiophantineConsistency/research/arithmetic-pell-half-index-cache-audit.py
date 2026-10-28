"""Read-only exact import/provider inventory for the proposed HalfIndex leaf.

No compiler, subprocess, overlay, source edit, or dependency refresh occurs.
All earlier inventories remain byte-for-byte unchanged.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
OUT = D / 'research/arithmetic-pell-half-index-cache-plan.json'
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


def accepted(relative, sha, manifest, manifest_sha, module):
    packet_pin, packet = load_pinned(relative, sha)
    manifest_pin, items = load_pinned(manifest, manifest_sha)
    require(packet['status'] == 'PASS', 'accepted packet status')
    for item in items:
        check(dict(item, path=str(ROOT / item['path'])))
    for row in packet['records']:
        require(row['exit_code'] == 0, 'accepted exit')
        for key in ['source', 'snapshot', 'object', 'log', 'timing']:
            check(row[key])
    for key in ['driver', 'state', 'durable_state', 'final_authentication']:
        if key in packet:
            check(packet[key])
    row = next(row for row in packet['records'] if row['module'] == module)
    return dict(module=module, source=row['source'], objects=[row['object']],
        imports=imports(row['source']['path']), supplement_packet=packet_pin,
        supplement_manifest=manifest_pin,
        provenance='Independently accepted ROOT main provider; Checks are evidence, not an import.')


require(not OUT.exists(), 'refuse overwrite')
parent_pin, parent = load_pinned('research/arithmetic-pell-index-divisibility-cache-plan.json',
    'ab6f041ac993f09ef46965feb906c3445da26d9c509a13ca7522c1b4a57a8274')
residue_pin, residue = load_pinned('research/arithmetic-pell-residue-classes-cache-plan.json',
    '542ca22a1f4f3a26ea5c987ae0c4b915d7be71275c560df8405786b97846c388')
for plan in [parent, residue]:
    for pin in plan['pins']:
        check(pin)
mods = {entry['module']: entry for entry in parent['modules']}
external = {entry['module']: entry for entry in parent['external']}
supplement_pin, supplement = load_pinned(
    'research/arithmetic-pell-index-divisibility-accepted-integral-solution.json',
    '1733d27dc9af570a50fc5983afdfb9b63c1c1ef8531f0419a547be23758dc60a')
for pin in supplement['pins']:
    check(pin)
entry = mods[supplement['module']]
require(entry['source'] == supplement['source'] and
        entry['objects'] == [supplement['old_object']], 'accepted Integral supplement')
entry['objects'] = [supplement['accepted_object']]
entry['provenance'] = 'Accepted ROOT IntegralSolution supplement, applied only in memory.'
require(parent['boundary_search'] == residue['boundary_search'], 'explicit boundary order')
require(parent['compiler'] == residue['compiler'], 'same compiler')
for entry in residue['modules']:
    name = entry['module']
    if name in mods:
        old = mods[name]
        require(old['source'] == entry['source'] and old['imports'] == entry['imports'],
                'overlap source/header: ' + name)
        require([(x['sha256'], x['bytes']) for x in old['objects']] ==
                [(x['sha256'], x['bytes']) for x in entry['objects']], 'overlap objects: ' + name)
    else:
        mods[name] = entry
for entry in residue['external']:
    require(external.get(entry['module']) == entry, 'same external boundary: ' + entry['module'])
for entry in [accepted('reviews/arithmetic-pell-index-divisibility-root-replay.json',
    'f85bd8718f4a36671954f76101b076be3712aa344e08f664d798c55936317ce8',
    'reviews/arithmetic-pell-index-divisibility-root-replay/FILES.json',
    'c5dfb147b371e5754db053dcd94a2338c34d373e65743be5542d6daab1d6c25f',
    'DiophantineConsistency.ArithmeticPellIndexDivisibility'),
    accepted('reviews/arithmetic-pell-residue-classes-root-replay.json',
    '03f4eb9c82e76f7b967bbc76d9559d5054de5d02528bac3f40728eedd757b33b',
    'reviews/arithmetic-pell-residue-classes-root-replay/FILES.json',
    'b84148a3d85901b2ef531c90b61f19410740ad37574d12de11cef5cba7c1e4b5',
    'DiophantineConsistency.ArithmeticPellResidueClasses')]:
    require(entry['module'] not in mods, 'new accepted main')
    mods[entry['module']] = entry
direct = ['DiophantineConsistency.ArithmeticPellIndexDivisibility',
          'DiophantineConsistency.ArithmeticPellResidueClasses']
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
            kind='Prospective private link, no overlay created'))
for item in boundary:
    check(item['source'])
    for obj in item['artifacts']:
        check(obj)
        relative = str(Path(*item['module'].split('.')[:-1]) / Path(obj['path']).name)
        require(relative not in virtual, 'boundary shadowing')
        first = next((Path(root) / relative for root in parent['boundary_search']
                      if (Path(root) / relative).is_file()), None)
        require(first is not None, 'missing actual boundary provider')
        providers.append(dict(module=item['module'], relative=relative, expected=obj,
            actual=check(dict(obj, path=str(first))), kind='Actual explicit boundary first provider'))
counts = dict(custom=len(order), Foundation=sum(x.startswith('Foundation.') for x in order),
    artifacts=len(virtual), external=len(boundary), boundary_artifacts=len(providers)-len(virtual),
    boundary_primaries=len(boundary), boundary_companions=len(providers)-len(virtual)-len(boundary),
    actual_first_providers=len(providers), fresh_prerequisites=0)
require(counts == dict(custom=106, Foundation=95, artifacts=391, external=38,
    boundary_artifacts=114, boundary_primaries=38, boundary_companions=76,
    actual_first_providers=505, fresh_prerequisites=0), 'exact proposed scope')
refs = []
for name in ['Carrier65', 'CurrentMaskData2011', 'CurrentCarrierArithmetic2011',
    'CurrentPolynomialWindow2011', 'NativePellBootstrap', 'NativePellFirstIndex',
    'NativePellStepDown', 'ArithmeticPellFirstNorm']:
    refs.append(check(record(D / ('Lean/DiophantineConsistency/' + name + '.lean'))))
for name in ['PellHalf90', 'PellDoubled', 'PellRelaxedMain']:
    refs.append(check(record(ROOT / ('Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/' + name + '.lean'))))
check(parent['compiler'])
check(record(__file__))
for pin in list(pins.values()):
    check(pin)
result = dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',
    parents=[parent_pin, residue_pin], accepted_integral_supplement=supplement_pin,
    direct_imports=direct, counts=counts, modules=[mods[name] for name in order],
    topological_order=order, external=boundary, boundary_search=parent['boundary_search'],
    compiler=parent['compiler'], artifact_providers=providers, references_only=refs,
    audit=record(__file__), pins=list(pins.values()), observations=observations,
    unique_paths=len(pins), scope='Proposed ArithmeticPellHalfIndex + Checks only; exact odd quotient '
    'transport and actual main-index recovery. All selected providers accepted. FirstNorm/native '
    'and Jones sources are references, not imported. No compiler, overlay, refresh, source/rank '
    'assumption, first-index/power/witness or final PA/HA equivalence claim. Existing package '
    'provenance qualifications inherited; current hashes do not claim a new dependency replay.')
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(plan=record(OUT), counts=counts, observations=observations,
                     unique_paths=len(pins)), indent=2))
