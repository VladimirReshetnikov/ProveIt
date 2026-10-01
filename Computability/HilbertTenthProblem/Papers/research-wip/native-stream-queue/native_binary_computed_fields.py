"""Paid positive graph definitions for native AND and packed tape kernels.

All source gates remain charged. The positive theorem requires q and F3
positive before equations; the three concrete callers prove this domain.
"""
import argparse
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import random

import sympy as sp
import native_binary_positive_scale as scale
import wang_b_packed_motion as motion
import langton_ant_packed_toggle_tape as toggle

DEFINITIONS = dict(a='R12', c='R10a', d='R14', k='R10b', r='bs_packed', s='bs_odd')
VARIANTS = dict(four=('a', 'd', 'k', 's'), six=tuple(DEFINITIONS))
polynomial_source = scale.polynomial_source
execute = scale.execute
ledger = scale.ledger


def rewrite(old, fields=VARIANTS['six'], prefix=''):
    """Exact graph substitution; caller supplies the positive q,F3 proof."""
    fields = tuple(fields)
    assert len(set(fields)) == len(fields) and set(fields) <= DEFINITIONS.keys()
    assert not old.get('native_computed_fields')
    scale.checked_source(old['source'], old['parameters'], old['auxiliaries'])
    name = lambda v: prefix+v if isinstance(v, str) else v
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    template, pairs, _ = scale.native.source('and64_prescribed')
    expected = [(name(n), op, name(a), name(b)) for n, op, a, b in template[7:]]
    scaled = bool(old.get('native_positive_scale'))
    if scaled:
        assert old['positive_scale_prefix'] == prefix
        expected = [(n, '*', name('bs_X_bound'), name('q')) if n == name('wn2') else
                    (n, op, a, b) for n, op, a, b in expected]
    assert all(rows[n] == (op, a, b) for n, op, a, b in expected)
    inherited = [(name(a), name(b)) for a, b in pairs
                 if not (scaled and (a, b) == ('bs_X_bound', 'wn2'))]
    assert all(old['comparisons'].count(pair) == 1 for pair in inherited)
    substitutions = {name(f): name(DEFINITIONS[f]) for f in fields}
    assert substitutions.keys() <= set(old['auxiliaries'])
    assert not substitutions.keys() & set(old.get('public_registers', {}).values())
    removed = [(n, rhs) for n, rhs in substitutions.items()]
    assert all(old['comparisons'].count(pair) == 1 for pair in removed)
    replace = lambda v: substitutions.get(v, v) if isinstance(v, str) else v
    source = [(n, op, replace(a), replace(b)) for n, op, a, b in old['source']]
    comparisons = [(replace(a), replace(b)) for a, b in old['comparisons'] if (a, b) not in removed]
    auxiliaries = [n for n in old['auxiliaries'] if n not in substitutions]
    source = scale.sort_source(source, old['parameters']+auxiliaries)
    scale.checked_source(source, old['parameters'], auxiliaries)
    packet = scale.metadata(dict(old, source=source, comparisons=comparisons, auxiliaries=auxiliaries,
        native_computed_fields=True, computed_fields=fields, computed_prefix=prefix,
        computed_substitutions=substitutions, computed_removed_comparisons=removed,
        computed_parent=old))
    assert Counter(op for _, op, _, _ in source) == Counter(op for _, op, _, _ in old['source'])
    assert packet['equations'] == old['equations']-len(fields)
    assert packet['witnesses'] == old['witnesses']-len(fields)
    return packet


def base(context='and', scaled=True):
    if context == 'and':
        packet = scale.build()
        return packet if scaled else packet['positive_scale_parent']
    parent = dict(motion=motion, toggle=toggle)[context].build()
    return scale.rewrite(parent, 'native__') if scaled else parent


def build(context='and', scaled=True, fields=VARIANTS['six']):
    return rewrite(base(context, scaled), fields, '' if context == 'and' else 'native__')


def lift_to_parent(packet, values):
    env = execute(packet['source'], values)
    return dict(values, **{n: env[rhs] for n, rhs in packet['computed_substitutions'].items()})


def project_from_parent(packet, values):
    return {n: v for n, v in values.items() if n not in packet['computed_substitutions']}


def source_closure(packet):
    source, output = polynomial_source(packet)
    nodes = {n: (a, b) for n, _, a, b in source}
    live = set()
    def visit(n):
        if n not in nodes or n in live:
            return
        live.add(n)
        for v in nodes[n]:
            if isinstance(v, str):
                visit(v)
    visit(output)
    assert live == set(nodes)


def audit(packet, cases, seed):
    rng = random.Random(seed)
    source, output = polynomial_source(packet)
    parent = packet['computed_parent']
    old_source, old_output = polynomial_source(parent)
    value = lambda env, v: env[v] if isinstance(v, str) else v
    assert len(old_source)-len(source) == 3*len(packet['computed_fields'])
    for case in range(cases):
        positive = case < cases//2
        values = {n: rng.randrange(1, 8) if positive else rng.randrange(-5, 6)
                  for n in packet['parameters']+packet['auxiliaries']}
        restored = lift_to_parent(packet, values)
        env, before = execute(source, values), execute(old_source, restored)
        assert all(env[n] == before[n] for n, _, _, _ in packet['source'])
        assert all(value(before, a) == value(before, b) for a, b in packet['computed_removed_comparisons'])
        expected = [value(before, a)-value(before, b) for a, b in parent['comparisons']
                    if (a, b) not in packet['computed_removed_comparisons']]
        actual = [value(env, a)-value(env, b) for a, b in packet['comparisons']]
        assert actual == expected and env[output] == before[old_output] == sum(r*r for r in actual)
        assert project_from_parent(packet, restored) == values
        if positive:
            assert min(restored.values()) > 0
        if parent.get('native_positive_scale'):
            raw = scale.lift_to_parent(parent, restored)
            raw_source, raw_output = polynomial_source(parent['positive_scale_parent'])
            assert execute(raw_source, raw)[raw_output] == env[output]
            if positive:
                assert min(raw.values()) > 0
    source_closure(packet)
    return dict(whole_output_identities=cases, signed_cases=cases//2,
                positive_graph_extensions=cases//2, round_trips=cases)


def degree_audit(packet):
    """Upper bound on the multivariate degree plus an exact slice witness."""
    bound = scale.degree_bound(packet)
    t = sp.Symbol('t')
    values = {n: sp.Poly((1+i%5)*t+i+1, t)
              for i, n in enumerate(packet['parameters']+packet['auxiliaries'])}
    env = execute(packet['source'], values)
    at = lambda v: env[v] if isinstance(v, str) else sp.Poly(v, t)
    residuals = [at(a)-at(b) for a, b in packet['comparisons']]
    maximum = max(r.degree() for r in residuals)
    lower = 2*maximum
    leading = sum(r.LC()**2 for r in residuals if r.degree() == maximum)
    assert leading > 0 and lower <= bound
    return dict(degree_upper_bound=bound, witnessed_degree_lower_bound=int(lower),
                exact_degree=int(bound) if lower == bound else None)


def outer_history_audit():
    rng = random.Random(137223)
    paths = steps = 0
    for context, host, outer_count in (('motion', motion, 3), ('toggle', toggle, 2)):
        for scaled in (False, True):
            for fields in VARIANTS.values():
                packet = build(context, scaled, fields)
                for case in range(16):
                    if context == 'motion':
                        actions = [rng.choice(('mark', 'stay', 'left', 'right')) for _ in range(1+case%6)]
                        old_values, trace = host.positive_path(case, 1<<6, actions)
                    else:
                        old_values, trace = host.positive_path(case, [1<<rng.randrange(8) for _ in range(1+case%6)])
                    # Keep the genuine outer history and choose arbitrary positive
                    # remaining native coordinates. These are not full Pell zeros.
                    values = {n: old_values[n] for n in packet['parameters']+packet['auxiliaries']}
                    restored = lift_to_parent(packet, values)
                    if scaled:
                        restored = scale.lift_to_parent(packet['computed_parent'], restored)
                    assert min(restored.values()) > 0
                    residuals, words, native_values = host.independent(restored)
                    assert residuals[:outer_count] == [0]*outer_count
                    assert words[0] & words[1] == words[2]
                    assert max(words) < native_values['P']
                    paths += 1
                    steps += trace['duration']
    return dict(genuine_outer_history_transfers=paths, chronological_rows=steps,
                scope='Outer histories and joined bit lanes only; not full positive Pell zeros.')


def verify():
    schedules, examples = [], []
    cases = 0
    # Every subset, including the unprojected source, receives actual-source
    # identities and a degree calculation. Exhaustiveness is only this family.
    for scaled in (False, True):
        for size in range(7):
            for fields in combinations(DEFINITIONS, size):
                packet = build(scaled=scaled, fields=fields)
                result = audit(packet, 16, 901108+len(schedules))
                cases += result['whole_output_identities']
                schedules.append(dict(scaled=scaled, fields=fields, ledger=ledger(packet),
                                      audit=result, degree=degree_audit(packet)))
    for context in ('and', 'motion', 'toggle'):
        for scaled in (False, True):
            for variant, fields in VARIANTS.items():
                packet = build(context, scaled, fields)
                result = audit(packet, 64, 223137+len(examples))
                cases += result['whole_output_identities']
                source, output = polynomial_source(packet)
                examples.append(dict(context=context, scaled=scaled, variant=variant,
                    ledger=ledger(packet), audit=result, parameters=packet['parameters'],
                    auxiliaries=packet['auxiliaries'], source=source, output=output))
    and_six = ledger(build())
    assert and_six['certificate'] == dict(operations=64, multiplications=33,
        additions_subtractions=31, equations=9, witnesses=15)
    assert and_six['polynomial']['operations'] == 90
    assert ledger(build('motion'))['polynomial']['operations'] == 223
    assert ledger(build('toggle'))['polynomial']['operations'] == 137
    frontier = []
    for rec in sorted(schedules, key=lambda r: (r['ledger']['polynomial']['operations'],
                                               r['degree']['degree_upper_bound'])):
        if not frontier or rec['degree']['degree_upper_bound'] < frontier[-1]['degree']['degree_upper_bound']:
            frontier.append({k: rec[k] for k in ('scaled', 'fields', 'ledger', 'degree')})
    return dict(status='PASS_NATIVE_BINARY_COMPUTED_FIELDS', schedules=schedules, examples=examples,
        standalone_operation_degree_frontier=frontier,
        outer_history_transfers=outer_history_audit(),
        complete_output_identities=cases, signed_cases=cases//2, positive_graph_extensions=cases//2,
        scope='Exact positive graph bijections for prescribed AND and the inherited motion/toggle relations. '
              'All64 definition subsets and both scale choices are enumerated only for standalone AND. '
              'Positive q,F3 domains are proved by the three callers. Component degree claims remain upper '
              'bounds. No full Pell zeros are numerically materialized; no new universal machine claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    for record in result['examples']:
        print(record['context'], record['scaled'], record['variant'], record['ledger'])
