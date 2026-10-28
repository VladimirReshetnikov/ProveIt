"""Read-only population prerequisite inventory; no compiler or overlay."""
from pathlib import Path
import hashlib
import json
import re
import shutil

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
pins = {}
observations = 0


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def record(path):
    path = Path(path)
    path = path if path.is_absolute() else R / path
    raw = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw))


def check(expected):
    global observations
    actual = record(expected['path'])
    need(actual['sha256'] == expected['sha256'], 'hash: ' + actual['path'])
    need('bytes' not in expected or actual['bytes'] == expected['bytes'], 'size')
    pins[actual['path']] = actual
    observations += 1
    return actual


def load(relative, sha):
    pin = check(dict(path=str(D / relative), sha256=sha))
    return pin, json.loads(Path(pin['path']).read_text())


def imports(path):
    text = Path(path).read_text()
    out = []
    index = depth = 0
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == '/-':
                depth += 1
                index += 2
            elif pair == '-/':
                depth -= 1
                index += 2
            else:
                out.append('\n' if text[index] == '\n' else ' ')
                index += 1
        elif pair == '/-':
            depth = 1
            index += 2
        elif pair == '--':
            while index < len(text) and text[index] != '\n':
                index += 1
        else:
            out.append(text[index])
            index += 1
    need(depth == 0, 'balanced comments')
    text = ''.join(out)
    result = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        result.extend(line.split())
    return list(dict.fromkeys(result))


output = D / 'research/arithmetic-binary-population-cache-plan.json'
need(not output.exists(), 'fresh plan')
need(shutil.disk_usage('/tmp').free >= 520 * 1024**2, 'reserve')
parent_pin, parent = load('research/arithmetic-pell-recurrence-cache-plan.json',
                          'dea799d5151a9a1024f975c2740d9aa23bf81a0965db5b60768b347242f95035')
peer_pin, peer = load('reviews/arithmetic-pell-recurrence-peer-replay.json',
                      'b581c5220c6ccc30e5ca6e7e29417cfb3c9464442661a990643f7a242ca691f0')
need(peer['status'] == 'PASS', 'accepted peer')
for name, sha in [('arithmetic-pell-recurrence-peer-replay/FILES.json',
                   '9c7535ec5686f71dff0ecae7f805f5337915b1f1118c1ab7ed19fdafbfd113d1'),
                  ('arithmetic-pell-recurrence-root-auth/FILES.json',
                   '8acd5bb42bc7f5c665a808e45310254008c415d7afcf1fac455272418257b91f')]:
    manifest_pin, entries = load('reviews/' + name, sha)
    for row in entries:
        check(dict(row, path=str(Path(manifest_pin['path']).parent / row['path'])))
for key in ['author_packet', 'state', 'inputs', 'driver', 'bundle_manifest']:
    check(peer[key])
for row in peer['records']:
    need(row['exit_code'] == 0 and row['matches_author'], 'successful independent replay')
    for key in ['source', 'snapshot', 'log', 'timing', 'object']:
        check(row[key])
for row in parent['pins']:
    check(row)
receipt = check(dict(path=str(D / 'reviews/arithmetic-pell-recurrence-root.md'),
                     sha256='f1ecbe385ec73f9748e2dec98f771ad83eb9714b20992fb1a3052d3bf4adef34'))
modules = {row['module']: row for row in parent['modules']}
external = {row['module']: row for row in parent['external']}
seen = set()
active = set()
used = set()
order = []


def visit(name):
    if name not in modules:
        need(name in external, 'known boundary: ' + name)
        used.add(name)
        return
    if name in seen:
        return
    need(name not in active, 'acyclic graph')
    active.add(name)
    row = modules[name]
    source = check(row['source'])
    need(imports(source['path']) == row['imports'], 'actual header: ' + name)
    for dependency in row['imports']:
        visit(dependency)
    for artifact in row['objects']:
        check(artifact)
    active.remove(name)
    seen.add(name)
    order.append(name)


direct = ['Foundation.FirstOrder.Arithmetic.HFS.PRF', 'Mathlib.Tactic.Ring']
for name in direct:
    visit(name)
need(seen == set(modules) and used == set(external), 'exact reachable closure')
search = [str(Path(peer['private']) / 'lib'), *parent['boundary_search']]
providers = []
for row in [modules[name] for name in order] + list(external.values()):
    if row['module'] in external:
        check(row['source'])
    for artifact in row.get('objects', row.get('artifacts')):
        relative = str(Path(*row['module'].split('.')[:-1]) / Path(artifact['path']).name)
        first = next((Path(root) / relative for root in search if (Path(root) / relative).is_file()), None)
        need(first is not None, 'available provider: ' + relative)
        actual = check(dict(artifact, path=str(first)))
        providers.append(dict(module=row['module'], relative=relative, expected=check(artifact), actual=actual))
counts = dict(custom=len(modules), Foundation=sum(name.startswith('Foundation.') for name in modules),
              artifacts=sum(len(row['objects']) for row in modules.values()), external=len(external),
              boundary_artifacts=sum(len(row['artifacts']) for row in external.values()),
              actual_first_providers=len(providers), fresh_prerequisites=0)
need(counts == dict(custom=95, Foundation=95, artifacts=380, external=38,
                    boundary_artifacts=114, actual_first_providers=494, fresh_prerequisites=0), 'exact scope')
check(parent['compiler'])
proposal = check(dict(path=str(D / 'research/arithmetic-binary-population-proposal.md'),
                      sha256='888c8e556ade5b865271dc8e7d06f156daf27f2b9dd96400eab3aab305455d58'))
auditor = check(record(__file__))
for row in list(pins.values()):
    check(row)
need(shutil.disk_usage('/tmp').free >= 520 * 1024**2, 'output reserve')
result = dict(status='READ_ONLY_AUTHENTICATED_PLAN_NO_COMPILER_OR_OVERLAY',
              parent=parent_pin, accepted_peer=peer_pin, accepted_receipt=receipt,
              proposal=proposal, auditor=auditor, direct_imports=direct, counts=counts,
              modules=[modules[name] for name in order], topological_order=order,
              external=list(external.values()), boundary_search=parent['boundary_search'],
              compiler=parent['compiler'], audited_existing_search=search, first_providers=providers,
              pins=list(pins.values()), observations=observations, unique_paths=len(pins),
              scope='Only two new population leaves; accepted PRF/Ring cached closure, no prerequisite rebuild. '
              'External package internals remain inherited boundaries. No compiler or overlay in this audit.')
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(plan=record(output), counts=counts, observations=observations,
                      unique_paths=len(pins)), indent=2))
