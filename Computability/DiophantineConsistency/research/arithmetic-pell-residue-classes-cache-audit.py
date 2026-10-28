"""Read-only source/cache audit for a proposed internal Pell residue-class leaf.

No compiler, subprocess, overlay, dependency refresh, or cache mutation occurs.
The only output is a new JSON inventory beside this script.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
BASE = DC / 'research/arithmetic-pell-periodicity-cache-plan.json'
PEER = DC / 'reviews/arithmetic-pell-periodicity-peer-replay.json'
OUT = DC / 'research/arithmetic-pell-residue-classes-cache-plan.json'
observations = {}


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def record(path):
    p = Path(path)
    data = p.read_bytes()
    return dict(path=str(p), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


def check(pin):
    actual = record(pin['path'])
    require(actual['sha256'] == pin['sha256'], 'hash: ' + pin['path'])
    if 'bytes' in pin:
        require(actual['bytes'] == pin['bytes'], 'size: ' + pin['path'])
    observations[actual['path']] = actual
    return actual


def observe(path):
    return check(record(path))


def imports(path):
    text = Path(path).read_text()
    out = []
    i = depth = 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            i += 2
        elif pair == '--':
            while i < len(text) and text[i] != '\n':
                i += 1
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, 'comment balance: ' + str(path))
    clean = ''.join(out)
    initial = [] if re.search(r'^\s*prelude\s*$', clean, re.M) else ['Init']
    names = [name for line in re.findall(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)', clean, re.M)
        for name in line.split()]
    return list(dict.fromkeys(initial + names))


check(dict(path=str(BASE), sha256='cf4cb17c055461bfcf7977b5e7ff3b1c2e4ab3f362ceedd6a12264cc8c552238'))
check(dict(path=str(PEER), sha256='5a4a46bb30bdcc70940c4ea683015297610fdcdd8cb9a53f6e03fcfca375f7ea'))
base = json.loads(BASE.read_text())
peer = json.loads(PEER.read_text())
main = peer['records'][0]
require(main['module'] == 'DiophantineConsistency.ArithmeticPellPeriodicity', 'main identity')
require(main['exit_code'] == 0 and main['object_byte_identical'] and main['log_byte_identical'],
        'accepted peer result')
for name in ['source', 'object', 'log', 'snapshot', 'timing']:
    check(main[name])
for pin in base['pins']:
    check(pin)
root_receipt = observe(DC / 'reviews/arithmetic-pell-periodicity-root.md')
root_manifest = check(dict(path=str(DC / 'reviews/arithmetic-pell-periodicity-root-auth/FILES.json'),
    sha256='3ba1c533b8006e863986e4405694b70a341804d3dcc4d7f39a6d2e040ecb75e4'))
for pin in json.loads(Path(root_manifest['path']).read_text()):
    check(dict(pin, path=str(ROOT / pin['path'])))
base['modules'].append(dict(module=main['module'], source=main['source'], objects=[main['object']],
    imports=['Init', 'DiophantineConsistency.ArithmeticPellCongruences'],
    provenance='Accepted Periodicity commit b4f140c632, independent peer object; root receipt and manifest pinned.'))
modules = {m['module']: m for m in base['modules']}
boundaries = {m['module']: m for m in base['external']}
visited, active, used_boundaries = set(), set(), set()


def visit(name):
    if name not in modules:
        require(name in boundaries, 'unknown boundary: ' + name)
        used_boundaries.add(name)
        return
    if name in visited:
        return
    require(name not in active, 'import cycle: ' + name)
    active.add(name)
    item = modules[name]
    check(item['source'])
    require(imports(item['source']['path']) == item['imports'], 'current header: ' + name)
    for obj in item['objects']:
        check(obj)
    for dep in item['imports']:
        visit(dep)
    active.remove(name)
    visited.add(name)


visit(main['module'])
require(visited == set(modules) and used_boundaries == set(boundaries), 'exact source closure')
boundary_providers = []
for item in base['external']:
    check(item['source'])
    for artifact in item['artifacts']:
        check(artifact)
        relative = Path(*item['module'].split('.')[:-1]) / Path(artifact['path']).name
        first = next((Path(root) / relative for root in base['boundary_search']
                      if (Path(root) / relative).is_file()), None)
        require(first is not None, 'boundary provider: ' + str(relative))
        actual = check(dict(artifact, path=str(first)))
        boundary_providers.append(dict(module=item['module'], first=actual, expected=artifact))
check(base['compiler'])
counts = dict(custom=len(modules), Foundation=sum(n.startswith('Foundation.') for n in modules),
    artifacts=sum(len(m['objects']) for m in modules.values()), external=len(boundaries),
    external_companions=len(boundary_providers), fresh_prerequisites=0)
require(counts == dict(custom=99, Foundation=95, artifacts=384, external=38,
                      external_companions=114, fresh_prerequisites=0), 'planned exact scope')
references = []
for name in ['NativePellFirstIndex', 'NativePellStepDown', 'NativePellBootstrap', 'NativePellPower',
             'SignedPellResidue', 'ArithmeticPellFirstNorm']:
    references.append(observe(DC / ('Lean/DiophantineConsistency/' + name + '.lean')))
for name in ['PellDoubled', 'PellRelaxedMain', 'PellHalf90']:
    references.append(observe(ROOT / ('Computability/HilbertTenthProblem/Lean/Diophantine/Paper1980/' + name + '.lean')))
references += [observe(DC / 'reviews/arithmetic-pell-first-norm-root.md'),
    observe('/home/codex/src/Proofs/.lake/packages/mathlib/Mathlib/NumberTheory/PellMatiyasevic.lean')]
observe(__file__)
base.update(status='READ_ONLY_PLAN_AUTHENTICATED_NO_BUILD', direct_imports=[main['module']],
    counts=counts, pins=list(observations.values()), boundary_providers=boundary_providers,
    references_only=references, parent_plan=record(BASE), accepted_supplement=record(PEER),
    supplement_root_receipt=root_receipt, supplement_root_manifest=root_manifest,
    scope=('Proposed two new residue-class leaves only. No source implementation, compiler, '
           'overlay or dependency refresh. Foundation/external bytes reuse the accepted package '
           'boundary; hashes authenticate current equality, not a new dependency proof replay. '
           'FirstNorm and native/Jones files are references only, not selected imports.'))
for pin in list(observations.values()):
    check(pin)
require(not OUT.exists(), 'refuse overwrite: ' + str(OUT))
OUT.write_text(json.dumps(base, indent=2) + '\n')
print(json.dumps(dict(output=record(OUT), counts=counts, distinct_observed_paths=len(observations),
                      compiler_executions=0, overlays_created=0)))
