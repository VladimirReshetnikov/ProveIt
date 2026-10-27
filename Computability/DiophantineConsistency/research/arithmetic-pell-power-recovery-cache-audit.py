"""Read-only provider audit for the proposed internal power-recovery checkpoint.

No compiler, subprocess, overlay, dependency refresh, or proof-source edit.
Existing accepted plans and provider evidence remain unchanged.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = ROOT / 'Computability/DiophantineConsistency'
OUT = D / 'research/arithmetic-pell-power-recovery-cache-plan.json'
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
                'inputs', 'providers', 'author', 'author_packet', 'author_manifest']:
        if key in packet:
            check(packet[key])
    row = next(row for row in packet['records'] if row['module'] == module)
    return dict(module=module, source=check(row['source']), objects=[check(row['object'])],
        imports=imports(row['source']['path']), supplement_packet=packet_pin,
        supplement_manifest=mf_pin, provenance=provenance)


# Independently accepted ROOT FirstIndex pins supplied after the math proposal froze.
ROOT_PACKET_SHA = 'ec7d159fd9be782bed9718ce2bc32008af9ec6cfea5a6686f18ad0f3f53b9643'
ROOT_MANIFEST_SHA = '000558fdfad7009fd4d5fdd63586773dcf7860095c1cff056a29345468cbf4c3'
require(not OUT.exists(), 'refuse overwrite')
require(not ROOT_PACKET_SHA.startswith('PENDING'), 'accepted ROOT FirstIndex pins required')
parent_pin, parent = load_pinned('research/arithmetic-pell-first-index-cache-plan.json',
    '0dd6cb70b70619b87f1c9986a1f6f3bc6c37d76bb575e461e19c21dafc7bc3a1')
for pin in parent['pins']:
    check(pin)
mods = {entry['module']: entry for entry in parent['modules']}
external = {entry['module']: entry for entry in parent['external']}
entry = accepted('reviews/arithmetic-pell-first-index-root-replay.json',
    ROOT_PACKET_SHA, 'reviews/arithmetic-pell-first-index-root-replay/FILES.json',
    ROOT_MANIFEST_SHA, 'DiophantineConsistency.ArithmeticPellFirstIndex',
    'Independently accepted ROOT FirstIndex main provider. Checks are evidence, not an import.')
# Reauthenticate the accepted leaf's exact compilation input and all507 providers.
root_packet = json.loads(Path(entry['supplement_packet']['path']).read_text())
root_state = json.loads(Path(check(root_packet['state'])['path']).read_text())
root_input = json.loads(Path(check(root_state['inputs'])['path']).read_text())
require(check(root_input['plan']) == parent_pin, 'ROOT used this exact parent inventory')
require(root_input['counts'] == parent['counts'], 'ROOT parent counts')
require(root_input['LEAN_PATH'][1:] == parent['boundary_search'], 'ROOT package search')
for key in ['proposal', 'compiler', 'providers', 'authentication']:
    check(root_input[key])
for item in root_input['sources']:
    check(item)
root_providers = json.loads(Path(root_input['providers']['path']).read_text())
require(len(root_providers) == parent['counts']['actual_first_providers'], 'ROOT provider count')
parent_providers = { (x['module'], Path(x['expected']['path']).name): x['expected']
                    for x in parent['artifact_providers'] }
for item in root_providers:
    expected, actual = check(item['expected']), check(item['actual'])
    require((expected['sha256'], expected['bytes']) ==
            (actual['sha256'], actual['bytes']), 'ROOT first provider bytes')
    old = parent_providers[(item['module'], Path(expected['path']).name)]
    require((old['sha256'], old['bytes']) == (actual['sha256'], actual['bytes']),
            'ROOT compared with exact prospective parent provider')
require(entry['module'] not in mods, 'new accepted main')
mods[entry['module']] = entry
direct = ['DiophantineConsistency.ArithmeticPellFirstIndex']
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
for name in ['Foundation.FirstOrder.Arithmetic.Exponential.Exp',
             'Foundation.FirstOrder.Arithmetic.Exponential.Log']:
    require(name in seen, 'represented base-two exponential already in closure')
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
require(counts == dict(custom=109, Foundation=95, artifacts=394, external=38,
    boundary_artifacts=114, boundary_primaries=38, boundary_companions=76,
    actual_first_providers=508, fresh_prerequisites=0), 'exact proposed scope')
refs = []
for name in ['Carrier65', 'CurrentMaskData2011', 'CurrentCarrierArithmetic2011',
             'NativePellPower', 'NativePellFirstIndex']:
    refs.append(check(record(D / ('Lean/DiophantineConsistency/' + name + '.lean'))))
refs.append(check(record(ROOT / 'Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/PellRatio90.lean')))
proposal = check(record(D / 'research/arithmetic-pell-power-recovery-proposal.md'))
check(parent['compiler'])
check(record(__file__))
for pin in list(pins.values()):
    check(pin)
result = dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',
    parents=[parent_pin], accepted_leaf_inputs=check(root_state['inputs']),
    accepted_leaf_parent_providers=len(root_providers), direct_imports=direct, counts=counts,
    modules=[mods[name] for name in order], topological_order=order,
    external=boundary, boundary_search=parent['boundary_search'], compiler=parent['compiler'],
    artifact_providers=providers, references_only=refs, proposal=proposal,
    audit=record(__file__), pins=list(pins.values()), observations=observations,
    unique_paths=len(pins), scope='Proposed ArithmeticPellPowerRecovery + Checks only. '
    'Actual literal transport and four additive norms plus beta>=15 imply X=Exp.exp R '
    'and the represented Exponential relation at arbitrary internal rank. Both indices '
    'are derived by accepted FirstIndex, not supplied. Constant-sixteen paired recurrence '
    'comparison and a positive projection quotient avoid external general-power/ratio '
    'oracles. No compiler, overlay, refresh or proof-source edits. Concrete internal '
    'port/polynomial certification, simultaneous cofinal witnesses and final PA/HA '
    'endpoints remain separate. All prior package provenance qualifications are '
    'inherited; source/object pins do not claim fresh dependency compilation. '
    '114 boundary artifacts means38 primaries plus76 companions, not114 companions.')
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(plan=record(OUT), counts=counts, observations=observations,
                     unique_paths=len(pins)), indent=2))
