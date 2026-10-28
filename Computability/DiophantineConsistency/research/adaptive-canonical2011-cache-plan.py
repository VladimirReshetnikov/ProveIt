"""Read-only source/object authentication for proposed adaptive converse leaves.

No Lean execution, project-code import, object creation/copy, or source edit.
Only this audit's new JSON output is written. Package imports are explicit
authenticated boundaries, not a claim to have replayed those packages.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path('/home/codex/.codex/worktrees/46be/Proofs')
DC = ROOT / 'Computability/DiophantineConsistency'
OUT = DC / 'research/adaptive-canonical2011-cache-plan.json'


def pin(path):
    path = Path(path)
    data = path.read_bytes()
    return dict(path=str(path), sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))


observations = {}


def check(record):
    actual = pin(record['path'])
    if actual['sha256'] != record['sha256']:
        raise ValueError(('changed pin', record, actual))
    observations[actual['path']] = actual
    return actual


def imports(path):
    # Strip line and nested block comments before reading import declarations.
    source = Path(path).read_text()
    out, i, depth = [], 0, 0
    while i < len(source):
        pair = source[i:i + 2]
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
            out.append(' ')
            i += 2
        elif pair == '--':
            while i < len(source) and source[i] != '\n':
                i += 1
        else:
            out.append(source[i])
            i += 1
    if depth:
        raise ValueError(('unterminated comment', path))
    lines = re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',
                       ''.join(out), re.M)
    return list(dict.fromkeys(['Init'] + [name for line in lines for name in line.split()]))


graph_root_path = DC / 'reviews/native-adaptive-graph-root-replay/ROOT.json'
ordinary_root_path = DC / 'reviews/native-ordinary-source-construction-root-replay/ROOT.json'
ordinary_author_path = DC / 'reviews/native-ordinary-source-construction-replay.json'
provider_pins = [
    dict(path=str(graph_root_path), sha256='be6d8ffe03204ca88e739bac4df4f44e39f96748b5ce81cc5672e287de40b4c7'),
    dict(path=str(ordinary_root_path), sha256='6c1fec344ba36d5f65db8aeaab0d20e4c70af88320ebdea5dc936a400d33cdbf'),
    dict(path=str(ordinary_author_path), sha256='c73617b3fd69519347f1b329b2167d2be394ec974ee17bbe7a540417c5d65d2b'),
]
providers = [check(r) for r in provider_pins]
graph_root = json.loads(graph_root_path.read_text())
ordinary_root = json.loads(ordinary_root_path.read_text())
ordinary_author = json.loads(ordinary_author_path.read_text())
if graph_root['status'] != 'PASS' or ordinary_root['status'] != 'PASS':
    raise ValueError('unaccepted provider')
graph_inputs_pin = graph_root['inputs']
ordinary_inputs_pin = ordinary_author['final']['state']['inputs']
check(graph_inputs_pin)
check(ordinary_inputs_pin)
graph_inputs = json.loads(Path(graph_inputs_pin['path']).read_text())
ordinary_inputs = json.loads(Path(ordinary_inputs_pin['path']).read_text())
providers += [graph_inputs_pin, ordinary_inputs_pin]
compiler = check(graph_inputs['compiler'])
if compiler['sha256'] != ordinary_inputs['compiler']['sha256']:
    raise ValueError('compiler mismatch')

custom = {}
overlap = []


def add_custom(record, provider, root, accepted_fresh=False):
    name = record['module']
    source = check(record['source'])
    original_object = check(record['object'])
    parsed = imports(source['path'])
    if 'actual_imports' in record and parsed != record['actual_imports']:
        raise ValueError(('import drift', name))
    local_path = Path(root) / 'lib' / Path(*name.split('.')).with_suffix('.olean')
    cache_object = check(dict(path=str(local_path), sha256=original_object['sha256']))
    new = dict(module=name, source=source, object=cache_object,
               original_object=original_object, actual_imports=parsed,
               provider=provider, accepted_fresh_in_provider=accepted_fresh)
    if name in custom:
        old = custom[name]
        if old['source']['sha256'] != source['sha256'] or \
                old['object']['sha256'] != cache_object['sha256']:
            raise ValueError(('provider overlap mismatch', name, old, new))
        overlap.append(dict(module=name, source_sha256=source['sha256'],
                            object_sha256=cache_object['sha256'],
                            selected_provider=old['provider'], agreeing_provider=provider))
    else:
        custom[name] = new


# Prefer the newly accepted graph overlay when the two accepted caches overlap.
for rec in graph_inputs['selected_custom']:
    add_custom(rec, str(graph_root_path), graph_root['private'])
graph_main = next(r for r in graph_root['records']
                  if r['module'] == 'DiophantineConsistency.NativeAdaptiveGraph')
if graph_main['exit_code'] != 0:
    raise ValueError('graph was not built')
add_custom(graph_main, str(graph_root_path), graph_root['private'], True)
for rec in ordinary_root['selected_custom']:
    add_custom(rec, str(ordinary_root_path), ordinary_root['private'])
ordinary_main = next(r for r in ordinary_root['completed']
                     if r['module'] == 'DiophantineConsistency.NativeOrdinarySourceConstruction')
if ordinary_main['exit_code'] != 0:
    raise ValueError('ordinary source was not built')
add_custom(ordinary_main, str(ordinary_root_path), ordinary_root['private'], True)

boundary = {}
for inp in [graph_inputs, ordinary_inputs]:
    for rec in inp['external_boundary']:
        name = rec['module']
        new = dict(module=name, source=check(rec['source']),
                   artifacts=[check(r) for r in rec['artifacts']])
        if name in boundary:
            old = boundary[name]
            if old != new:
                raise ValueError(('boundary disagreement', name, old, new))
        else:
            boundary[name] = new


def closure(roots):
    seen, visiting, ordered, edges = set(), set(), [], set()

    def walk(name):
        if name not in custom:
            if name not in boundary:
                raise ValueError(('unknown import', name))
            edges.add(name)
            return
        if name in visiting:
            raise ValueError(('import cycle', name))
        if name in seen:
            return
        visiting.add(name)
        for dep in custom[name]['actual_imports']:
            walk(dep)
        visiting.remove(name)
        seen.add(name)
        ordered.append(name)

    for root in roots:
        walk(root)
    return dict(imports=roots, custom_topological=ordered,
                external_boundaries=sorted(edges),
                counts=dict(custom=len(ordered), external=len(edges),
                            external_companions=sum(len(boundary[e]['artifacts']) for e in edges)))


canonical = closure(['DiophantineConsistency.NativeAdaptiveGraph',
                     'DiophantineConsistency.Carrier66Source'])
current = closure(['DiophantineConsistency.NativeAdaptiveGraph',
                   'DiophantineConsistency.Carrier66Source',
                   'DiophantineConsistency.NativeOrdinarySourceConstruction'])
if set(current['custom_topological']) != set(custom):
    raise ValueError(('unneeded provider modules', sorted(set(custom) - set(current['custom_topological']))))
if set(current['external_boundaries']) != set(boundary):
    raise ValueError('unneeded boundary entries')

result = dict(status='READ_ONLY_AUTHENTICATED_PLAN',
              scope='No compiler or dependency refresh; exact current source/object pins and direct '
                    'package boundaries checked. Proposed fresh canonical/current leaves do not yet '
                    'exist and are excluded from these cached counts. No whole-package replay claim.',
              providers=providers, compiler=compiler, audit_script=pin(__file__),
              canonical=canonical, current=current,
              selected_custom=[custom[n] for n in current['custom_topological']],
              external_boundary=[boundary[n] for n in sorted(boundary)],
              agreeing_overlaps=overlap, observation_count=len(observations),
              observations=list(observations.values()))
OUT.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(dict(status=result['status'], canonical=canonical['counts'],
                      current=current['counts'], overlaps=len(overlap),
                      observations=len(observations), output=pin(OUT)), indent=2))
