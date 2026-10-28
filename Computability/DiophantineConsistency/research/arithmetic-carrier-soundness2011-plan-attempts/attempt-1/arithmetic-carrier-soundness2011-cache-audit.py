"""Read-only exact source/provider union; no compiler, subprocess or overlay.

Inputs are immutable accepted arithmetic and narrow-syntax evidence. Newly
listed direct package imports are explicit package boundaries, not a claim
that their entire transitive Mathlib/compiler closure was freshly rebuilt.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
CENTRAL = Path('/home/codex/src/Proofs')
OUT = DC / 'research/arithmetic-carrier-soundness2011-cache-plan.json'
PROPOSAL = DC / 'research/arithmetic-carrier-soundness2011-proposal.md'
pins = {}; observations = 0


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def absolute(path):
    path = Path(path)
    return path if path.is_absolute() else ROOT / path


def record(path):
    path = absolute(path); data = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def check(expected):
    global observations
    actual = record(expected['path'])
    require(actual['sha256'] == expected['sha256'], 'hash '+str(expected['path']))
    require('bytes' not in expected or expected['bytes'] == actual['bytes'], 'bytes '+str(expected['path']))
    pins[actual['path']] = actual; observations += 1
    return actual


def load(relative, sha):
    pin = check(dict(path=str(DC/relative), sha256=sha))
    return pin, json.loads(Path(pin['path']).read_text())


def nested(value):
    if isinstance(value, dict):
        if isinstance(value.get('path'), str) and isinstance(value.get('sha256'), str):
            check(value)
        for item in value.values(): nested(item)
    elif isinstance(value, list):
        for item in value: nested(item)


def imports(path):
    source = Path(path).read_text(); out = []; i = depth = 0
    while i < len(source):
        pair = source[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: out.append('\n' if source[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            while i < len(source) and source[i] != '\n': i += 1
        else: out.append(source[i]); i += 1
    require(depth == 0, 'comment balance')
    clean = ''.join(out)
    initial = [] if re.search(r'^\s*prelude\s*$', clean, re.M) else ['Init']
    return list(dict.fromkeys(initial + [name for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', clean, re.M)
        for name in line.split()]))


def accepted(relative, sha, manifest_path, manifest_sha, module):
    packet_pin, packet = load(relative, sha)
    mf_pin, mf = load(manifest_path, manifest_sha)
    require(packet['status'] == 'PASS', 'accepted packet status')
    for item in mf: check(item)
    for row in packet['records']:
        require(row['exit_code'] == 0, 'accepted command status')
        for key in ['source','snapshot','object','log','timing']: check(row[key])
    for key in ['state','durable_state','driver','inputs','providers','final_authentication',
                'author_packet','author_receipt','author_manifest']:
        if key in packet: nested(packet[key])
    row = next(x for x in packet['records'] if x['module'] == module)
    source = check(row['source']); obj = check(row['object'])
    return dict(module=module, source=source, objects=[obj], imports=imports(source['path']),
        provenance='Independently accepted leaf; both command records and manifest authenticated',
        accepted_packet=packet_pin, accepted_manifest=mf_pin), packet


require(not OUT.exists(), 'refuse overwrite')
require(shutil.disk_usage('/tmp').free >= 512*1024**2+4*1024**2, '512MiB reserve')
parent_pin, parent = load('research/arithmetic-pell-power-recovery-cache-plan.json',
    '2884c1845d1c273ad9139dfc5955970271f62846b61f667efff0921a6d88e2ad')
for pin in parent['pins']: check(pin)
mods = {x['module']: x for x in parent['modules']}
boundary = {x['module']: x for x in parent['external']}
negative, neg_packet = accepted('reviews/arithmetic-negative-norms-root-replay.json',
    '7cd7d5aac0e95c8ec667fd48893bee78c9586721cc4bee565b9f4e2434668da8',
    'reviews/arithmetic-negative-norms-root-replay/FILES.json',
    'e7923caa75638f609caa189744dadfd241f79c7fd5eb8f5e4b98d7c2c573201a',
    'DiophantineConsistency.ArithmeticNegativeNorms')
signed, signed_packet = accepted('reviews/arithmetic-signed-pairs-peer-replay.json',
    'd78a4c6b7d3382be629a144d029e054f06c8f20461dbb4f8f31dc83c1b90450e',
    'reviews/arithmetic-signed-pairs-peer-replay/FILES.json',
    '9aa69627e17db6289cdc14f5c719ac03e43f9c98debdd404fb60cd331c7a8524',
    'DiophantineConsistency.ArithmeticSignedPairs')
accept_pin, signed_accept = load('reviews/arithmetic-signed-pairs-root-acceptance.json',
    'b736aca4c2fb44cf6b783fe4a37c17a7135524c24cca6843829392164f260a42')
require(signed_accept['status'] == 'PASS', 'SignedPairs root acceptance')
for pin in signed_accept['pins']: check(pin)
mods[negative['module']] = negative; mods[signed['module']] = signed

narrow_pin, narrow = load('reviews/current-equation-narrow-dependency-replay.json',
    'eaf7d6e5a2fce01c5bed6b49347436269311e9395de45355b318f8179c05eb6f')
root_pin, narrow_root = load('reviews/current-equation-narrow-root-replay/ROOT.json',
    'c9f6fe79c65027d685c3c1e2d1e5197c160a145cb24c00b5424a4579846b6983')
require(narrow_root['state']['status'] == 'PASS', 'narrow accepted status')
require(narrow_root['state']['packet_sha256'] == narrow_pin['sha256'], 'narrow author binding')
for name, sha in narrow_root['files'].items():
    check(dict(path=str(DC/'reviews/current-equation-narrow-root-replay'/name), sha256=sha))
for pin in narrow['pins']: check(pin)
# Exact declared source/object compilation provenance is retained from the
# accepted receipt, including source-identical caches and recorded traces.
narrow_rows = {}
for item in narrow['modules']:
    source = check(dict(path=str(absolute(item['source'])), sha256=item['source_sha256']))
    objects = [check(x) for x in item['objects']] if 'objects' in item else [
        check(dict(path=item['object'], sha256=item['object_sha256']))]
    for key in ['trace','cache_source','log','snapshot']:
        if key in item and key+'_sha256' in item:
            check(dict(path=item[key], sha256=item[key+'_sha256']))
    narrow_rows[item['module']] = dict(module=item['module'], source=source,
        objects=objects, imports=imports(source['path']), provenance=narrow_pin,
        original_record=item)
for item in narrow_root['state']['completed']:
    require(item['exit_code'] == 0 and item['matches_author'], 'narrow replay result')
    source = check(dict(path=item['source'], sha256=item['source_sha256']))
    obj = check(dict(path=item['object'], sha256=item['object_sha256']))
    check(dict(path=item['log'], sha256=item['log_sha256']))
    narrow_rows[item['module']] = dict(module=item['module'], source=source,
        objects=[obj], imports=imports(source['path']), provenance=root_pin,
        original_record=item)
overlap = []
for name, item in narrow_rows.items():
    if name in mods:
        old = mods[name]
        require(item['source']['sha256'] == old['source']['sha256'], 'overlap source '+name)
        old_hashes = {Path(x['path']).name: x['sha256'] for x in old['objects']}
        new_hashes = {Path(x['path']).name: x['sha256'] for x in item['objects']}
        require(old_hashes == new_hashes, 'overlap artifacts '+name)
        overlap.append(dict(module=name, source=old['source'], objects=old_hashes))
    else: mods[name] = item

visited = set(); active = set(); order = []; external_used = set()

def visit(name):
    if name not in mods:
        require(name == 'Init' or name.startswith(('Mathlib.','Aesop','Qq','Lean','Batteries.')),
                'unreviewed project import '+name)
        external_used.add(name); return
    if name in visited: return
    require(name not in active, 'import cycle '+name); active.add(name)
    item = mods[name]; check(item['source'])
    require(imports(item['source']['path']) == item['imports'], 'header changed '+name)
    for child in item['imports']: visit(child)
    for obj in item['objects']: check(obj)
    active.remove(name); visited.add(name); order.append(name)


direct = ['DiophantineConsistency.ArithmeticNegativeNorms',
    'DiophantineConsistency.ArithmeticSignedPairs',
    'DiophantineConsistency.ArithmeticPellFirstIndex',
    'DiophantineConsistency.CurrentEquationSyntax2011']
for name in direct: visit(name)
# The package boundary is the same pinned 4.32 package set as both accepted
# parents. Additional direct names receive explicit source/object/trace pins.
for filename, values in narrow['package_identity'].items():
    check(dict(path=str(ROOT/filename), sha256=values['current_sha256']))
    check(dict(path=str(CENTRAL/filename), sha256=values['cache_sha256']))
check(parent['compiler']); check(narrow['compiler'])
new_external = []
for name in sorted(external_used):
    if name not in boundary:
        require(name.startswith('Mathlib.'), 'new non-Mathlib boundary '+name)
        pkg = CENTRAL/'.lake/packages/mathlib'; rel = Path(*name.split('.'))
        source = check(record(pkg/rel.with_suffix('.lean')))
        base = pkg/'.lake/build/lib/lean'/rel
        artifacts = [check(record(str(base)+suffix)) for suffix in
                     ['.olean','.olean.private','.olean.server']]
        trace = check(record(str(base)+'.trace')); data = json.loads(Path(trace['path']).read_text())
        recorded = data['outputs']['o']; hash_files = []
        for artifact in artifacts:
            ap = Path(artifact['path']); suffix = ap.name[len(rel.name):]
            hp = check(record(str(ap)+'.hash')); value = Path(hp['path']).read_text().strip()
            require(value+suffix in recorded, 'package trace output '+name+suffix)
            hash_files.append(hp)
        boundary[name] = dict(module=name, source=source, artifacts=artifacts,
            provenance='Explicit additional direct package boundary at accepted package identity; no transitive rebuild claim',
            trace=trace, output_lake_hash_files=hash_files)
        new_external.append(name)
    item = boundary[name]; check(item['source'])
    for artifact in item['artifacts']: check(artifact)
external = [boundary[name] for name in sorted(external_used)]
# Existing accepted libraries only. This is an observed first-provider
# mapping, not a new overlay and not a compiler invocation.
first_root = '/tmp/arithmetic-pell-first-index-root-obnhr4v8/lib'
narrow_root_provider = '/tmp/current-equation-narrow-root-peer-0kiizsdx/lib'
search = [neg_packet['private_provider'], signed_packet['private_provider'],
          first_root, narrow_root_provider, *parent['boundary_search']]
providers = []
for item in [mods[name] for name in order]+external:
    for expected in item.get('objects', item.get('artifacts')):
        relative = Path(*item['module'].split('.')[:-1])/Path(expected['path']).name
        actual = next((Path(base)/relative for base in search if (Path(base)/relative).is_file()), None)
        require(actual is not None, 'missing provider '+str(relative))
        actual_pin = check(dict(expected, path=str(actual)))
        providers.append(dict(module=item['module'], relative=str(relative),
            expected=expected, actual=actual_pin))
counts = dict(custom=len(order), Foundation=sum(n.startswith('Foundation.') for n in order),
    artifacts=sum(len(mods[n]['objects']) for n in order), external=len(external),
    boundary_primaries=len(external), boundary_companions=sum(len(x['artifacts'])-1 for x in external),
    boundary_artifacts=sum(len(x['artifacts']) for x in external),
    actual_first_providers=len(providers), fresh_prerequisites=0)
require(counts == dict(custom=135, Foundation=95, artifacts=420, external=50,
    boundary_primaries=50, boundary_companions=100, boundary_artifacts=150,
    actual_first_providers=570, fresh_prerequisites=0), 'exact proposed scope')
references = [check(record(DC/('Lean/DiophantineConsistency/'+name+'.lean'))) for name in
    ['ObjectCurrentEquation2011','Carrier65','ArithmeticPellPowerRecovery','CurrentMasks2011']]
check(record(PROPOSAL)); check(record(__file__))
for pin in list(pins.values()): check(pin)
require(shutil.disk_usage('/tmp').free >= 512*1024**2+4*1024**2, 'output reserve')
result = dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',
    scope='Actual maintained splitNatural positive zero to five additive equations, including signed factor binding before transport and actual narrow-data port bounds; proposed pair only',
    proposal=record(PROPOSAL), audit=record(__file__), parents=[parent_pin,narrow_pin,root_pin],
    negative_packet=negative['accepted_packet'], signed_packet=signed['accepted_packet'],
    signed_root_acceptance=accept_pin, direct_imports=direct, counts=counts,
    modules=[mods[n] for n in order], topological_order=order, overlaps=overlap,
    external=external, additional_package_boundaries=new_external,
    compiler=parent['compiler'], boundary_search=parent['boundary_search'],
    audited_existing_search=search, first_providers=providers,
    references_only_not_imports=references, pins=list(pins.values()),
    observations=observations, unique_paths=len(pins), free_bytes=shutil.disk_usage('/tmp').free,
    cache_scope='No prerequisite compiled here. Source-authenticated accepted custom modules and explicit existing package boundary artifacts; no package transitive-source closure claim.')
OUT.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(dict(inventory=record(OUT), counts=counts, overlaps=len(overlap),
    additional_boundaries=new_external, observations=observations,
    unique_paths=len(pins), free_bytes=shutil.disk_usage('/tmp').free), indent=2))
