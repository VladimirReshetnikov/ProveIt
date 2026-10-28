"""Independent read-only ROOT verification of the concrete radix client plan."""
from pathlib import Path
import hashlib
import json
import re
import shutil

R = Path('/home/codex/.codex/worktrees/46be/Proofs')
D = R / 'Computability/DiophantineConsistency'
pins = {}
comparisons = 0


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def record(path):
    path = Path(path)
    path = path if path.is_absolute() else R / path
    raw = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(raw).hexdigest(), bytes=len(raw))


def check(expected):
    global comparisons
    actual = record(expected['path'])
    need(actual['sha256'] == expected['sha256'], 'hash: ' + actual['path'])
    need('bytes' not in expected or actual['bytes'] == expected['bytes'], 'size')
    pins[actual['path']] = actual
    comparisons += 1
    return actual


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
    names = [] if re.search(r'^\s*prelude\s*$', text, re.M) else ['Init']
    for line in re.findall(r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', text, re.M):
        names.extend(line.split())
    return list(dict.fromkeys(names))


manifest = check(dict(path=str(D / 'research/arithmetic-carrier-radix2011-plan-evidence/FILES.json'),
                      sha256='61297390c85d67b2a609ef97252eef4165fec45cd978f1f5780bf913cf60cb6e'))
entries = json.loads(Path(manifest['path']).read_text())
need(len(entries) == 9, 'nine frozen plan files')
for entry in entries:
    check(entry)
plan_pin = check(dict(path=str(D / 'research/arithmetic-carrier-radix2011-cache-plan.json'),
                      sha256='ac2fa36f63fd5ce826656a9096f7b3241a086a362ec1c41850555fb6a142c32e'))
plan = json.loads(Path(plan_pin['path']).read_text())
for entry in plan['pins']:
    check(entry)
modules = {row['module']: row for row in plan['modules']}
external = {row['module']: row for row in plan['external']}
seen = set()
active = set()
used = set()
order = []
artifacts = {}


def add(module, expected):
    actual = check(expected)
    relative = str(Path(*module.split('.')[:-1]) / Path(actual['path']).name)
    need(relative not in artifacts, 'unique artifact: ' + relative)
    artifacts[relative] = (module, actual['sha256'])


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
    need(not row.get('refresh', False), 'no prerequisite refresh')
    for dependency in row['imports']:
        visit(dependency)
    for entry in row['objects']:
        add(name, entry)
    active.remove(name)
    seen.add(name)
    order.append(name)


for name in plan['direct_imports']:
    visit(name)
need(seen == set(modules) and used == set(external), 'exact reachable union')
need(order == plan['topological_order'], 'dependency order')
for name, row in external.items():
    check(row['source'])
    for entry in row['artifacts']:
        add(name, entry)
matched = set()
for row in plan['first_providers']:
    relative = row['relative']
    actual = check(row['actual'])
    check(row['expected'])
    need(artifacts[relative] == (row['module'], actual['sha256']), 'artifact mapping')
    need(relative not in matched, 'unique provider')
    first = next((Path(root) / relative for root in plan['audited_existing_search']
                  if (Path(root) / relative).is_file()), None)
    need(first is not None and first.resolve() == Path(actual['path']).resolve(), 'first provider')
    matched.add(relative)
need(matched == set(artifacts), 'complete provider coverage')
counts = dict(custom=len(modules), Foundation=sum(name.startswith('Foundation.') for name in modules),
              artifacts=sum(len(row['objects']) for row in modules.values()),
              boundaries=len(external), boundary_artifacts=sum(len(row['artifacts']) for row in external.values()),
              providers=len(matched))
need(counts == dict(custom=138, Foundation=95, artifacts=423, boundaries=50,
                    boundary_artifacts=150, providers=573), 'exact profile')
need(plan['counts']['fresh_prerequisites'] == 0, 'zero refreshes')
check(plan['compiler'])
check(record(__file__))
for entry in list(pins.values()):
    check(entry)
need(shutil.disk_usage('/tmp').free >= 512 * 1024**2, 'reserve')
output = D / 'reviews/arithmetic-carrier-radix2011-plan-root.json'
need(not output.exists(), 'fresh ROOT audit')
result = dict(status='ROOT_READ_ONLY_REVIEW_PASS', plan=plan_pin, manifest=manifest,
              counts=counts, comparisons=comparisons, unique_paths=len(pins),
              pins=list(pins.values()), driver=record(__file__),
              qualification='Independent source/header DAG, complete pin and actual first-provider verification. '
              'Proposal and planner reviewed separately. No compiler, overlay or prerequisite refresh.')
output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(status=result['status'], counts=counts, comparisons=comparisons,
                      unique_paths=len(pins), output=record(output)), indent=2))
