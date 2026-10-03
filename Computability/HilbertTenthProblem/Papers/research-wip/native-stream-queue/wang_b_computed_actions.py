"""Positive edge definitions remove four Wang action coordinates/equations.

The optional bound schedule uses J+Ihat+Lhat+Rhat=2J-Ejump+3.
It preserves each chosen parent's complete positive zero set by a graph
bijection. It does not instantiate a universal Wang program.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import wang_b_packed_program as parent

scale = parent.positive_scale
execute = parent.execute
HATS = ('I_hat', 'L_hat', 'R_hat', 'Stay_hat')


def remap_tree(value, replace):
    if isinstance(value, str):
        return replace(value)
    if isinstance(value, dict):
        return {k: remap_tree(v, replace) for k, v in value.items()}
    if isinstance(value, list):
        return [remap_tree(v, replace) for v in value]
    if isinstance(value, tuple):
        return tuple(remap_tree(v, replace) for v in value)
    return value


def rewrite(old, *, fold_bound=True):
    assert not old.get('wang_computed_actions')
    # Only the frozen compiler's actual selected form is supported. Native
    # helper parents remain historical; no helper is replayed after this map.
    checked = parent.build(old['program'], old['literal_input'], old['form'])
    for key in ('source', 'comparisons', 'parameters', 'auxiliaries', 'interfaces'):
        assert old[key] == checked[key], key
    assert old.get('public_registers', {}) == checked.get('public_registers', {})
    rows = {n: (op, a, b) for n, op, a, b in old['source']}
    consumers = lambda v: {n for n, _, a, b in old['source'] if v in (a, b)}
    interface = old['interfaces']
    aliases, removed, definitions = {}, [], {}
    for raw, hat in zip(('I', 'L', 'R'), HATS):
        name = interface[raw]
        assert rows[name] == ('-', hat, 1)
        pairs = [pair for pair in old['comparisons'] if pair[0] == name]
        assert len(pairs) == 1
        pair = pairs[0]
        removed.append(pair)
        aliases[name] = definitions[hat] = pair[1]
    J, partition = interface['J'], interface['partition']
    removed.append((partition, J))
    assert old['comparisons'].count((partition, J)) == 1
    aliases[J] = partition
    op, total3, constant = rows[J]
    assert (op, constant) == ('-', 4)
    op, total2, stay = rows[total3]
    assert (op, stay) == ('+', 'Stay_hat')
    op, total1, right = rows[total2]
    assert (op, right) == ('+', 'R_hat')
    assert rows[total1] == ('+', 'I_hat', 'L_hat')
    assert consumers(total1) == {total2} and consumers(total2) == {total3}
    assert consumers(total3) == {J} and consumers('Stay_hat') == {total3}
    assert all(hat in old['auxiliaries'] and hat not in old['parameters'] for hat in HATS)
    drop = {interface[a] for a in ('I', 'L', 'R')} | {J, total1, total2, total3}
    if interface['jump_mask'] is None:
        jump = 0
    else:
        assert rows[interface['jump_mask']][:2] == ('*', interface['Bm1'])
        jump = rows[interface['jump_mask']][2]
    definitions['Stay_hat'] = jump
    additions = []
    bound_gates = 0
    changed_bound_prefix = set()
    if fold_bound:
        for hat in HATS[:3]:
            uses = [row for row in old['source'] if row[3] == hat and row[0] not in drop]
            assert len(uses) == 1
            n, op, before, _ = uses[0]
            assert op == '+'
            drop.add(n)
            aliases[n] = before
        bound_start = [n for n, op, a, b in old['source'] if (op, a, b) == ('+', J, 'T_hat')]
        assert len(bound_start) == 1
        current, encountered = bound_start[0], set()
        while encountered != set(HATS[:3]):
            changed_bound_prefix.add(current)
            encountered |= set(rows[current][1:]) & set(HATS[:3])
            if encountered != set(HATS[:3]):
                successors = [n for n, op, a, b in old['source'] if op == '+' and a == current]
                assert len(successors) == 1
                current = successors[0]
        base = 'computed_actions_bound_base'
        if jump == partition:
            # Every edge is a jump; the existing exact sum is already J.
            assert all(e['action'] == 'J' for e in old['edges'])
            additions = [(base, '+', partition, 3)]
        elif jump == 0:
            assert all(e['action'] != 'J' for e in old['edges'])
            additions = [('computed_actions_twice_J', '+', partition, partition),
                         (base, '+', 'computed_actions_twice_J', 3)]
        else:
            additions = [('computed_actions_twice_J', '+', partition, partition),
                         ('computed_actions_bound_before3', '-', 'computed_actions_twice_J', jump),
                         (base, '+', 'computed_actions_bound_before3', 3)]
        bound_gates = len(additions)
    else:
        additions = [(hat, '+', definitions[hat], 1) for hat in HATS[:3]]
    def replace(value):
        seen = set()
        while isinstance(value, str) and value in aliases:
            assert value not in seen
            seen.add(value)
            value = aliases[value]
        return value
    source = []
    for n, op, a, b in old['source']:
        if n in drop:
            continue
        if fold_bound and n == bound_start[0]:
            a = base
        source.append((n, op, replace(a), replace(b)))
    source += [(n, op, replace(a), replace(b)) for n, op, a, b in additions]
    auxiliaries = [n for n in old['auxiliaries'] if n not in HATS]
    source = scale.sort_source(source, old['parameters']+auxiliaries)
    known = scale.checked_source(source, old['parameters'], auxiliaries)
    interfaces = remap_tree(interface, replace)
    public = remap_tree(old.get('public_registers', {}), replace)
    for v in parent.units.register_leaves(interfaces) | parent.units.register_leaves(public):
        assert v in known, ('stale public register', v)
    packet = scale.metadata(dict(old, source=source, auxiliaries=auxiliaries,
        comparisons=[tuple(replace(v) for v in pair) for pair in old['comparisons'] if pair not in removed],
        interfaces=interfaces, public_registers=public,
        wang_computed_actions=True, action_parent=old, fold_action_bound=fold_bound,
        action_definitions=definitions, action_aliases=aliases,
        action_removed_comparisons=removed, action_deleted_registers=sorted(drop),
        action_reassociated_bound_prefix=sorted(changed_bound_prefix),
        action_bound_gates=bound_gates,
        outer_equations=old['outer_equations']-4,
        historical_native_parents_unchanged=True))
    saved = 10-bound_gates if fold_bound else 4
    assert packet['operations'] == old['operations']-saved
    assert packet['multiplications'] == old['multiplications']
    assert packet['additions_subtractions'] == old['additions_subtractions']-saved
    assert packet['equations'] == old['equations']-4
    assert packet['witnesses'] == old['witnesses']-4
    assert packet['outer_equations'] == 4
    assert all(not set(HATS) & set(pair) for pair in packet['comparisons'])
    if old.get('native_norm_units'):
        for n, op, a, b in source:
            if n.startswith('native__'):
                assert rows[n] == (op, a, b)
        assert packet['unit_factors'] == old['unit_factors']
    return packet


def build(program=parent.DEFAULT, literal_input=False, form='units', *, fold_bound=True):
    return rewrite(parent.build(program, literal_input, form), fold_bound=fold_bound)


polynomial_source = parent.polynomial_source
ledger = parent.ledger


def lift_to_parent(packet, values):
    env = execute(packet['source'], values)
    value = lambda v: env[v] if isinstance(v, str) else v
    return dict(values, **{hat: value(raw)+1 for hat, raw in packet['action_definitions'].items()})


def project_from_parent(packet, values):
    return {n: v for n, v in values.items() if n not in HATS}


def raw_lift(packet, values):
    return parent.raw_lift(packet['action_parent'], lift_to_parent(packet, values))


def closure(packet, *, sos=False):
    source, output = (parent.units.polynomial_source(packet, sum_of_squares=sos)
                      if packet.get('native_norm_units') else polynomial_source(packet))
    rows = {n: (a, b) for n, _, a, b in source}
    seen = set()
    def visit(v):
        if not isinstance(v, str) or v not in rows or v in seen:
            return
        seen.add(v)
        for child in rows[v]:
            visit(child)
    visit(output)
    assert len(rows) == len(source) and seen == set(rows)


def audit(packet, seed, cases=16):
    rng = random.Random(seed)
    old = packet['action_parent']
    source, out = polynomial_source(packet)
    old_source, old_out = polynomial_source(old)
    outputs = 0
    for case in range(cases):
        positive = case < cases//2
        draw = lambda: rng.randrange(1, 6) if positive else rng.randrange(-4, 5)
        values = {n: draw() for n in packet['parameters']+packet['auxiliaries']}
        if case == 0:
            # Every edge word is zero. All four restored hats must still
            # be positive before equations; the outer bound rejects J=0.
            values.update({f'edge{i}_hat': 1 for i in range(len(packet['edges']))})
        restored = lift_to_parent(packet, values)
        env, before = execute(source, values), execute(old_source, restored)
        at = lambda e, v: e[v] if isinstance(v, str) else v
        for n, _, _, _ in old['source']:
            if n in env and n not in packet['action_reassociated_bound_prefix']:
                assert env[n] == before[n]
            elif n in packet['action_aliases']:
                alias = packet['action_aliases'][n]
                while isinstance(alias, str) and alias in packet['action_aliases']:
                    alias = packet['action_aliases'][alias]
                # Folded bound partial sums intentionally change; their
                # aliases preserve the final bound, not each old prefix.
                if n in (old['interfaces']['I'], old['interfaces']['L'], old['interfaces']['R'], old['interfaces']['J']):
                    assert before[n] == at(env, alias)
        assert all(at(before, a) == at(before, b) for a, b in packet['action_removed_comparisons'])
        expected = [at(before, a)-at(before, b) for a, b in old['comparisons'] if (a, b) not in packet['action_removed_comparisons']]
        actual = [at(env, a)-at(env, b) for a, b in packet['comparisons']]
        assert actual == expected and env[out] == before[old_out]
        assert project_from_parent(packet, restored) == values
        if positive:
            assert min(restored.values()) > 0
        outputs += 1
        if packet.get('native_norm_units'):
            ss, so = parent.units.polynomial_source(packet, sum_of_squares=True)
            os, oo = parent.units.polynomial_source(old, sum_of_squares=True)
            assert execute(ss, values)[so] == execute(os, restored)[oo]
            outputs += 1
    closure(packet)
    if packet.get('native_norm_units'):
        closure(packet, sos=True)
    return dict(assignments=cases, signed_assignments=cases//2,
                full_output_identities=outputs, positive_graph_lifts=cases//2,
                coordinate_round_trips=cases)


def outer_histories(programs):
    rng = random.Random(331333)
    cases = steps = absent = singleton = 0
    for program in programs:
      for trial in range(8):
        head = 1 << rng.randrange(2, 5)
        x = rng.randrange(1, 32)
        trace = parent.run(program, x*head, head, 24)
        if not trace['halted']:
            continue
        for literal in (False, True):
          old_values, trace = parent.positive_history(program, x*head, head, 24, literal)
          for fold in (False, True):
            packet = build(program, literal, 'raw', fold_bound=fold)
            values = project_from_parent(packet, old_values)
            restored = lift_to_parent(packet, values)
            assert restored == old_values
            env = execute(packet['source'], values)
            at = lambda v: env[v] if isinstance(v, str) else v
            assert all(at(a) == at(b) for a, b in packet['comparisons'][:4])
            f = packet['interfaces']
            A, M, Z = (env[f[n]] for n in ('joined_H', 'joined_M', 'joined_Z'))
            assert A & M == Z and max(A, M, Z) < env[f['native_scale']]
            assert min(restored.values()) > 0
            cases += 1
            steps += len(trace['rows'])
            absent += any(all(e['action'] != a for e in packet['edges']) for a in ('M', 'L', 'R', 'J'))
            singleton += len(packet['edges']) == 1
    return dict(cases=cases, chronological_rows=steps,
                cases_with_absent_action=absent, singleton_edge_cases=singleton,
                scope='Actual outer histories and exact graph maps; native auxiliaries are placeholders, not full Pell zeros.')


def verify():
    programs = [('M',), ('L',), ('R',), (('J', 1),), parent.DEFAULT,
                ('M', ('J', 2)), ('L', 'R', ('J', 1)), tuple(['M']*19)]
    records = []
    for program in programs:
      for literal in (False, True):
       for form in ('raw', 'scaled', 'projected', 'units'):
        for fold in (False, True):
            packet = build(program, literal, form, fold_bound=fold)
            new, old = ledger(packet), ledger(packet['action_parent'])
            if form == 'units':
                assert all(new[k]['degree_upper_bound'] == old[k]['degree_upper_bound'] for k in ('product', 'SOS'))
            else:
                assert new['polynomial']['degree_upper_bound'] == old['polynomial']['degree_upper_bound']
            source, output = polynomial_source(packet)
            records.append(dict(program=program, literal_input=literal, form=form, fold_bound=fold,
                bound_gates=packet['action_bound_gates'], ledger=new,
                audit=audit(packet, 331333+len(records)), source=source, output=output,
                auxiliaries=packet['auxiliaries'], interfaces=packet['interfaces']))
    default = {form: ledger(build(form=form)) for form in ('raw', 'scaled', 'projected', 'units')}
    literal = {form: ledger(build(literal_input=True, form=form)) for form in ('raw', 'scaled', 'projected', 'units')}
    assert default['units']['product']['operations'] == 331
    assert literal['units']['product']['operations'] == 333
    invalid = dict(parent.build(), public_registers={'port': 'bound_sum_33'})
    try:
        rewrite(invalid)
    except AssertionError:
        rejected_export = True
    else:
        raise AssertionError('An added export of a reassociated bound prefix was accepted.')
    return dict(status='PASS_WANG_B_COMPUTED_ACTIONS', ledgers=records,
        assignment_audits=sum(r['audit']['assignments'] for r in records),
        signed_assignments=sum(r['audit']['signed_assignments'] for r in records),
        full_output_identities=sum(r['audit']['full_output_identities'] for r in records),
        outer_histories=outer_histories(programs), default=default, literal_default=literal,
        plain_default=ledger(build(fold_bound=False)),
        plain_literal_default=ledger(build(literal_input=True, fold_bound=False)),
        added_reassociated_prefix_export_rejected=rejected_export,
        scope='Positive graph bijection to each chosen fixed-program Wang parent, both input interfaces. '
              'No universal Wang instruction table or TM input morphism is instantiated.')


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
    print(result['default']['units'])
    print(result['literal_default']['units'])
    print(result['outer_histories'])
