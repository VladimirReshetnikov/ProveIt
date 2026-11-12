#!/usr/bin/env python3
"""Reconstruct a bounded, read-only lexical provider/stage plan. Never invokes Lean."""
from pathlib import Path
import hashlib
import json
import sys

if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):
    raise SystemExit('Use python3 -I -S -B')

D = Path(__file__).resolve().parents[2]
SLIM = D / 'research/ordinary14-root74-slim-overlay'
SURVEY = D / 'research/ordinary14-root74-provider-survey/observation.json'
P72 = Path('/tmp/p72-current-base-extension-attempt02-20261105/lib')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
sha = lambda data: hashlib.sha256(data).hexdigest()

inventory_bytes = (SLIM / 'inventory.json').read_bytes()
survey_bytes = SURVEY.read_bytes()
assert sha(inventory_bytes) == 'b3317a1aa674fd67708aef94685af953126fcd1f30ead3bd43a9afb95467583e'
assert sha(survey_bytes) == '14732a54d8f2d3592d31f78d731497a1d804780ca8ec643e3851314868e7b4ab'
inv = json.loads(inventory_bytes)
survey = json.loads(survey_bytes)
new = survey['slim_cut_new_sources']
frontier = survey['slim_cut_frontier']
external = survey['slim_cut_external']
assert new == sorted([
    'DiophantineConsistency.Compact44.FreeJ13',
    'DiophantineConsistency.Compact44.FreeJ13Halt',
    'DiophantineConsistency.DiscreteOrderedRingFacts'])
assert len(frontier) == 31 and len(external) == 4

def obj(root, module):
    return root.joinpath(*module.split('.')).with_suffix('.olean')

def evidence(path):
    assert path.is_file(), str(path)
    return {'path': str(path), 'realpath': str(path.resolve(strict=True)),
            'sha256': sha(path.read_bytes())}

objects = {name: evidence(obj(P72, name)) for name in frontier}
external_objects = {name: evidence(obj(PACKAGE, name)) for name in sorted(external)}
assert external_objects == external
assert all(not obj(P72, name).exists() for name in new)

# Fixed topological choice, not a validated Lean build order. All imports below
# are the pinned previous inventory's lexical headers, not lean --deps output.
first = [new[2], new[0], new[1]]
stages = []
done = set(frontier) | set(external)
for name in first:
    row = inv['project_sources'][name]
    source = D / row['path']
    assert sha(source.read_bytes()) == row['sha256']
    assert set(row['imports']) <= done, (name, set(row['imports']) - done)
    stages.append({'module': name, 'kind': 'qualified-source-candidate',
                   'source': str(source.relative_to(D)), 'sha256': row['sha256'],
                   'lexical_imports': row['imports']})
    done.add(name)

assert len(inv['drafts_topological']) == 159
for row in inv['drafts_topological']:
    name = row['module']
    source = SLIM / row['path']
    assert sha(source.read_bytes()) == row['overlay_sha256']
    imports = row['bare_imports'] + row['qualified_imports']
    assert set(imports) <= done, (name, set(imports) - done)
    assert name not in done
    stages.append({'module': name, 'kind': 'bare-inert-overlay',
                   'source': str(source.relative_to(D)), 'sha256': row['overlay_sha256'],
                   'lexical_imports': imports})
    done.add(name)
assert len(stages) == 162 and stages[-1]['module'] == 'Root74Endpoint'
print(json.dumps({
    'scope': 'bounded lexical candidate only; no Lean, runtime resolution, complete provider ancestry, build authorization or proof claim',
    'inventory_sha256': sha(inventory_bytes), 'survey_sha256': sha(survey_bytes),
    'qualified_frontier_objects': objects, 'external_cut_objects': external_objects,
    'candidate_stages': stages,
}, sort_keys=True, indent=2))
