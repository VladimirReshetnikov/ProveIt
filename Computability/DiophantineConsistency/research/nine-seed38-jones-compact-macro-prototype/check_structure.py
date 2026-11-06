#!/usr/bin/env python3
"""Validate DAG scope/topology and reject sample corruptions; not a Lean proof."""
import copy
import hashlib
import json
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
raw = (P / 'recipe.json').read_bytes()
data = json.loads(raw)


def validate(recipe):
    if recipe['schema'] != 'named-ring-dag-with-finite-sum-macros-v1' or recipe['inputs'] != 9:
        raise ValueError('schema')
    if recipe['seed'] != 'SharingSeed38.seed CurrentWindowCarry2011.ports' or recipe['seed_type'] != 'Expr (Fin 39)':
        raise ValueError('seed')
    if recipe['coefficient_definitions'] != {
        'z': 'ExecutableJones.indexZ seed 0', 'y': 'ExecutableJones.indexY seed 0',
        'pcoef': 'ExecutableJones.pCoefficient seed k', 'expo': 'ExecutableJones.codingExpo 38 4 k',
        'star': 'ExecutableJones.codingStar 38 4'}:
        raise ValueError('coefficient macros')
    seen = {}
    variables = set()
    refs = {}

    def nat(e, indices, stars):
        if not isinstance(e, list) or not e:
            raise ValueError('nat form')
        op = e[0]
        if op == 'lit' and len(e) == 2 and type(e[1]) is int and e[1] >= 0:
            return
        if op == 'index' and len(e) == 2 and e[1] in indices:
            return
        if op == 'expo' and len(e) == 2 and e[1] in stars:
            return
        if op in ('add', 'sub', 'mul', 'pow') and len(e) == 3:
            nat(e[1], indices, stars); nat(e[2], indices, stars); return
        raise ValueError(('nat op', e))

    def ring(e, indices, stars, dependencies):
        if not isinstance(e, list) or not e:
            raise ValueError('ring form')
        op = e[0]
        if op == 'const' and len(e) == 2 and type(e[1]) is int:
            return
        if op == 'var' and len(e) == 2 and type(e[1]) is int and 0 <= e[1] < 9:
            variables.add(e[1]); return
        if op == 'fixed' and len(e) == 2 and e[1] in ('z', 'y'):
            return
        if op == 'pcoef' and len(e) == 2 and e[1] in stars:
            return
        if op == 'ref' and len(e) == 2 and e[1] in seen:
            dependencies.add(e[1]); return
        if op in ('add', 'sub', 'mul') and len(e) == 3:
            ring(e[1], indices, stars, dependencies); ring(e[2], indices, stars, dependencies); return
        if op == 'pow' and len(e) == 3:
            ring(e[1], indices, stars, dependencies); nat(e[2], indices, stars); return
        if op == 'sum_range' and len(e) == 4 and isinstance(e[1], str) and e[1] not in indices | stars:
            nat(e[2], indices, stars); ring(e[3], indices | {e[1]}, stars, dependencies); return
        if op == 'sum_star' and len(e) == 3 and isinstance(e[1], str) and e[1] not in indices | stars:
            ring(e[2], indices, stars | {e[1]}, dependencies); return
        raise ValueError(('ring op, reference or scope', e))

    for row in recipe['nodes']:
        if set(row) != {'name', 'expr'} or not isinstance(row['name'], str) or row['name'] in seen:
            raise ValueError('node name')
        deps = set()
        ring(row['expr'], set(), set(), deps)
        seen[row['name']] = row['expr']
        refs[row['name']] = deps
    if recipe['output'] not in seen or variables != set(range(9)):
        raise ValueError('output or inputs')
    live = set()
    def mark(name):
        if name in live: return
        live.add(name)
        for dep in refs[name]: mark(dep)
    mark(recipe['output'])
    if live != set(seen):
        raise ValueError(('dead nodes', sorted(set(seen) - live)))
    return {'nodes': len(seen), 'live_nodes': len(live), 'inputs': sorted(variables)}


summary = validate(data)
mutations = []
bad = copy.deepcopy(data); bad['nodes'][0]['expr'] = ['ref', 'b']; mutations.append(bad)
bad = copy.deepcopy(data); bad['nodes'][0]['expr'] = ['var', 9]; mutations.append(bad)
bad = copy.deepcopy(data); bad['nodes'][0]['expr'] = ['pcoef', 'k']; mutations.append(bad)
bad = copy.deepcopy(data); bad['nodes'].append({'name': 'dead', 'expr': ['const', 0]}); mutations.append(bad)
for bad in mutations:
    try: validate(bad)
    except (ValueError, KeyError, TypeError): continue
    raise RuntimeError('mutation unexpectedly accepted')
print(json.dumps({'status': 'PASS_STRUCTURAL_CHECK_ONLY', **summary,
                  'rejected_mutations': len(mutations), 'recipe_sha256': hashlib.sha256(raw).hexdigest(),
                  'scope': 'Syntax/topology/binders and finite controls only; no semantic equality to Lean or document.'}, sort_keys=True))
