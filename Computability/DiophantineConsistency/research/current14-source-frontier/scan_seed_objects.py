#!/usr/bin/env python3
"""Find exact historical seed hashes among five local providers, read-only.

This is an observational scan, not a source-to-object or ancestry audit.
"""
import hashlib
import json
import sys
from pathlib import Path

if not __debug__:
    raise RuntimeError('assertions required; do not use Python -O')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
manifest_bytes = (HERE / 'historical-manifest.json').read_bytes()
assert hashlib.sha256(manifest_bytes).hexdigest() == 'ad373be2f3dbecd4beae4e44141c163f86294641e18bd9e4eacf000396fe0581'
prep = ROOT / 'Computability/DiophantineConsistency/reviews/ipra-standard-current14-historical-pair-terminal/preparation.json'
prep_bytes = prep.read_bytes()
assert hashlib.sha256(prep_bytes).hexdigest() == '53cedecdd1e357cbb800a51a783fa4cf7c0c01591e493080e7c7576bb2767d9d'
manifest = json.loads(manifest_bytes)
frontier_bytes = (HERE / 'result.json').read_bytes()
assert hashlib.sha256(frontier_bytes).hexdigest() == '5392cded531449193da23a695a165eaf1cefcdae2df3a1f9a1700c83acd234a7'
frontier = json.loads(frontier_bytes)
sources = manifest['sources']
seen, stack = set(), [manifest['target']]
while stack:
    module = stack.pop()
    if module in seen or module not in sources:
        continue
    seen.add(module)
    stack.extend(sources[module]['imports'])
need = seen - set(frontier['affected_on_historical_graph'])
seeds = json.loads(prep_bytes)['seeds']['author']
providers = [Path(p) for p in [
    '/tmp/direct80-coherent-rebuild-u2iz4c67/lib',
    '/tmp/trace74-direct-four-block-1zltaw2f/lib',
    '/tmp/p65-post-merge-replay/lib',
    '/tmp/derivation-endpoint-combined-20261031',
    '/tmp/adaptive13-main-orientation-ke21opyr/lib',
]]
cache, matches, unmatched = {}, [], []
for index, module in enumerate(sorted(need)):
    name = module.replace('.', '/') + '.olean'
    expected = seeds[name]
    found = None
    for provider in providers:
        path = provider / name
        if not path.is_file():
            continue
        resolved = str(path.resolve())
        if resolved not in cache:
            cache[resolved] = hashlib.sha256(path.read_bytes()).hexdigest()
        if cache[resolved] == expected:
            found = str(path)
            break
    if found:
        matches.append([module, found])
    else:
        unmatched.append(module)
    if index and index % 200 == 0:
        print(f'checked {index}, matched {len(matches)}', file=sys.stderr, flush=True)
print(json.dumps({'checked': len(need), 'matched': len(matches), 'unmatched': unmatched,
                  'paths': matches,
                  'scope': 'exact seed object bytes only; no transitive ancestry or rebuild verified'}, indent=2))
