"""Read-only minimal cache inventory for the internal Pell recurrence.
No compiler invocation, cache copying or project Python imports.
"""
from pathlib import Path
import hashlib, json, re

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
PARENT = DC / 'reviews/arithmetic-enum-soundnessperm222-root-replay/inputs.json'
RECEIPT = DC / 'reviews/arithmetic-enum-soundnessperm222-root.md'

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def record(path):
    p = Path(path); b = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))

def check(x):
    actual = record(x['path'])
    require(actual['sha256'] == x['sha256'], 'hash ' + x['path'])
    return actual

def imports(path):
    s = Path(path).read_text(); out = []; i = depth = 0
    while i < len(s):
        t = s[i:i+2]
        if depth:
            if t == '/-':
                depth += 1; i += 2
            elif t == '-/':
                depth -= 1; i += 2
            else:
                out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif t == '/-':
            depth = 1; i += 2
        elif t == '--':
            while i < len(s) and s[i] != '\n':
                i += 1
        else:
            out.append(s[i]); i += 1
    require(depth == 0, 'balanced comments')
    names, header = ['Init'], True
    for line in ''.join(out).splitlines():
        t = line.strip()
        if not t or t == 'module':
            continue
        m = re.fullmatch(r'(?:(?:public|private|meta)\s+)*import\s+([A-Za-z_][A-Za-z_0-9. ]*)', t)
        if m:
            require(header, 'late import ' + str(path))
            names.extend(m[1].split())
        else:
            header = False
    return list(dict.fromkeys(names))

parent = json.loads(PARENT.read_text())
modules = {m['module']: m for m in parent['modules']}
roots = ['Foundation.FirstOrder.Arithmetic.HFS.PRF', 'Mathlib.Tactic.Ring']
order, done, active, boundary = [], set(), set(), set()

def visit(name):
    if name in done:
        return
    if name not in modules:
        boundary.add(name); return
    require(name not in active, 'import cycle')
    active.add(name)
    item = modules[name]
    require(imports(item['source']) == item['imports'], 'current header ' + name)
    for dependency in item['imports']:
        visit(dependency)
    active.remove(name); done.add(name); order.append(name)

for root in roots:
    visit(root)
pins = [record(PARENT), record(RECEIPT), record(__file__), check(parent['compiler'])]
selected = []
for name in order:
    item = modules[name]
    source = check(dict(path=item['source'], sha256=item['source_sha256']))
    objects = [check(x) for x in item['objects']]
    pins.extend([source, *objects])
    selected.append(dict(module=name, source=source, objects=objects,
                         imports=item['imports'], provenance=item['provenance']))
oldpins = {x['path']: x for x in parent['pins']}
search = parent['lean_path'].split(':')[1:]
external = []
for name in sorted(boundary):
    relative = name.replace('.', '/')
    candidates = [Path(p) / (relative + '.olean') for p in search]
    candidates = [p for p in candidates if p.is_file()]
    require(len(candidates) == 1, 'unique boundary ' + name)
    obj = candidates[0]
    require(str(obj) in oldpins, 'accepted boundary object ' + name)
    check(oldpins[str(obj)])
    artifacts = []
    for suffix in ['', '.private', '.server']:
        p = Path(str(obj) + suffix)
        require(p.is_file(), 'boundary companion ' + str(p))
        if str(p) in oldpins:
            check(oldpins[str(p)])
        artifacts.append(record(p))
    if '/.lake/build/lib/lean/' in str(obj):
        source = Path(str(obj).split('/.lake/build/lib/lean/')[0]) / (relative + '.lean')
    else:
        source = Path(parent['compiler']['path']).parents[1] / 'src/lean' / (relative + '.lean')
    require(source.is_file(), 'boundary source ' + name)
    entry = dict(module=name, source=record(source), artifacts=artifacts)
    external.append(entry); pins.extend([entry['source'], *artifacts])
counts = dict(custom=len(selected), Foundation=sum(x['module'].startswith('Foundation.') for x in selected),
              artifacts=sum(len(x['objects']) for x in selected), external=len(external),
              external_companions=sum(len(x['artifacts']) for x in external), fresh_prerequisites=0)
require(counts == dict(custom=95, Foundation=95, artifacts=380, external=38,
                       external_companions=114, fresh_prerequisites=0), 'exact narrow scope')
for x in pins:
    check(x)
out = dict(status='READ_ONLY_PLAN_NO_COMPILATION', direct_imports=roots,
           counts=counts, modules=selected, external=external, pins=pins,
           compiler=parent['compiler'], boundary_search=search,
           scope='Two new arithmetic Pell recurrence leaves only; no existing source refresh, '
                 'Foundation build, source-checker or machine import. Classification, congruences, '
                 'cofinal witness construction and the final PA/HA equivalence remain open.')
target = DC / 'research/arithmetic-pell-recurrence-cache-plan.json'
target.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(dict(output=record(target), counts=counts, pins=len(pins))))
