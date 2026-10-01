"""Specialize duplicate padded idle selectors to zero, with paid pack plans.

Every output is exactly the parent polynomial with those positive hats set
to one. Equality of accepted ordinary inputs uses the macro-path theorem;
it is not a bijection with all parent positive tuples.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import group_projective_shared_flow_target as parent

execute = parent.execute
residuals = parent.residuals


def repunit_cost(n):
    assert n >= 1
    additions = n.bit_count()-1
    return dict(M=additions-int(n > 1 and n % 2 == 1), A=additions)


def rewrite(old):
    m = old['m']
    active = 1+sum(map(len, old['codes']))
    padding = m-active
    assert 1 <= active <= m and old['edges'][0] == (0, 0, 0)
    assert all(edge == (0, 0, 0) for edge in old['edges'][active:])
    assert all(1 <= edge[2] <= 8 for edge in old['edges'][1:active])
    if not padding:
        return dict(old, frozen_idle_padding=True, active_edges=active,
                    frozen_idle_count=0, frozen_idle_coordinates=[],
                    frozen_idle_saving=dict(M=0, A=0, operations=0),
                    frozen_idle_plan='identity', frozen_idle_changed_registers=[])
    rows = {row[0]: row for row in old['source']}
    P = 'controller__geometry_power' if old['compute_length'] else 'P'
    frozen = [f'controller__edge_hat{i}' for i in range(active, m)]
    assert all(n in old['auxiliaries'] for n in frozen)

    def power(j):
        if j == 0:
            return P
        name = f'controller__lane_power{j}'
        prior = P if j == 1 else f'controller__lane_power{j-1}'
        assert rows[name] == (name, '*', prior, prior)
        return name

    def dyadic_repunit(j):
        if j == 0:
            return 1
        if j == 1:
            name = 'controller__lane_factor0'
            assert rows[name] == (name, '+', P, 1)
            return name
        name = f'controller__lane_repunit{j-1}'
        factor = f'controller__lane_factor{j-1}'
        assert rows[factor] == (factor, '+', power(j-1), 1)
        assert rows[name] == (name, '*', dyadic_repunit(j-1), factor)
        return name

    full_repunit = dyadic_repunit(old['h'])
    # Audit and remove precisely the parent's m-lane positive-hat pack.
    removed_pack = set()
    value = f'controller__edge_hat{m-1}'
    for i in range(m-2, -1, -1):
        product = f'controller__edge_pack_mult{i}'
        total = f'controller__edge_pack_sum{i}'
        assert rows[product] == (product, '*', P, value)
        assert rows[total] == (total, '+', f'controller__edge_hat{i}', product)
        removed_pack.update((product, total))
        value = total
    word = 'controller__edge_word'
    assert rows[word] == (word, '-', value, full_repunit)
    assert {n for n in rows if n.startswith('controller__edge_pack_')} == removed_pack
    assert all({user for user, _, a, b in old['source'] if n in (a, b)}
               <= removed_pack | {word} for n in removed_pack)
    assert not any(n in pair for n in removed_pack for pair in old['comparisons'])

    # The padded hats are the final terms of the hub checksum group.
    hub = old['flow']['groups']['hub']
    live_hub = [i for i in hub if i < active]
    assert live_hub and hub == live_hub+list(range(active, m))
    value = f'controller__edge_hat{hub[0]}'
    removed_hub = set()
    live_hub_sum = f'controller__edge_hat{live_hub[0]}'
    for j, edge in enumerate(hub[1:], 1):
        name = f'controller__flow_raw_hub{j}'
        assert rows[name] == (name, '+', value, f'controller__edge_hat{edge}')
        if edge >= active:
            removed_hub.add(name)
        else:
            live_hub_sum = name
        value = name
    old_hub_sum = value
    checksum = rows['computed_J'][2]
    assert rows['computed_J'] == ('computed_J', '-', checksum, m)
    allowed = removed_hub | {'computed_J'} | ({checksum} if checksum != old_hub_sum else set())
    assert all({user for user, _, a, b in old['source'] if n in (a, b)} <= allowed
               for n in removed_hub)
    assert not any(n in pair for n in removed_hub for pair in old['comparisons'])
    if checksum != old_hub_sum:
        assert rows[checksum][1] == '+' and rows[checksum][3] == old_hub_sum
        assert {user for user, _, a, b in old['source'] if checksum in (a, b)} == {'computed_J'}
    for n in frozen:
        assert {user for user, _, a, b in old['source'] if n in (a, b)} <= removed_pack | removed_hub
        assert not any(n in pair for pair in old['comparisons'])

    def plan(kind):
        added = []
        def emit(name, op, a, b):
            if op == '*' and b == 1:
                return a
            added.append((name, op, a, b))
            return name
        def repunit(n):
            j = n.bit_length()-1
            high = 1 << j
            if high == n:
                return dyadic_repunit(j)
            low = repunit(n-high)
            prod = emit(f'frozen_idle_R{n}_product', '*', power(j), low)
            return emit(f'frozen_idle_R{n}', '+', dyadic_repunit(j), prod)
        if kind == 'trim':
            subtrahend = repunit(active)
            value = f'controller__edge_hat{active-1}'
            indices = range(active-2, -1, -1)
        else:
            value, subtrahend = repunit(padding), full_repunit
            indices = range(active-1, -1, -1)
        repunit_gates = len(added)
        for i in indices:
            prod = emit(f'frozen_idle_pack_mult{i}', '*', P, value)
            value = emit(f'frozen_idle_pack_sum{i}', '+', f'controller__edge_hat{i}', prod)
        added.append((word, '-', value, subtrahend))
        counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in added)
        n = active if kind == 'trim' else padding
        rc = repunit_cost(n)
        assert repunit_gates == rc['M']+rc['A']
        expected = (dict(M=active-1+rc['M'], A=active+rc['A']) if kind == 'trim'
                    else dict(M=active-int(padding == 1)+rc['M'], A=active+1+rc['A']))
        assert all(counts[key] == expected[key] for key in ('M', 'A'))
        return dict(kind=kind, source=added, operations=len(added), counts=expected,
                    repunit_length=n, repunit_cost=rc)

    plans = [plan('trim'), plan('tail')]
    chosen = min(plans, key=lambda p:(p['operations'], p['counts']['M'], p['kind']))
    source = []
    removed = removed_pack | removed_hub | {word}
    for name, op, a, b in old['source']:
        if name in removed:
            continue
        if name == 'computed_J':
            a = live_hub_sum if checksum == old_hub_sum else checksum
            b = active
        elif name == checksum:
            assert b == old_hub_sum
            b = live_hub_sum
        source.append((name, op, a, b))
    source += chosen['source']
    auxiliaries = [n for n in old['auxiliaries'] if n not in frozen]
    source = parent.ports.shared.factored.index.parent.sort_source(source, {'x', *auxiliaries})
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    saving = dict(M=old['multiplications']-counts['M'],
                  A=old['additions_subtractions']-counts['A'],
                  operations=old['operations']-len(source))
    # The hub checksum saves padding additions; the old pack has (m-1)M+mA.
    assert saving['M'] == m-1-chosen['counts']['M']
    assert saving['A'] == 2*m-active-chosen['counts']['A']
    assert saving['operations'] == saving['M']+saving['A'] >= 2*padding
    assert not any(n in (a, b) for n in frozen for _, _, a, b in source)
    changed = [checksum] if checksum != old_hub_sum else []
    return dict(old, source=source, auxiliaries=auxiliaries, operations=len(source),
        multiplications=counts['M'], additions_subtractions=counts['A'],
        positive_witnesses=len(auxiliaries), frozen_idle_padding=True,
        active_edges=active, frozen_idle_count=padding, frozen_idle_coordinates=frozen,
        frozen_idle_saving=saving, frozen_idle_plan=chosen['kind'],
        frozen_idle_changed_registers=changed, frozen_idle_pack_plans=plans,
        frozen_idle_removed_registers=sorted(removed))


def build(codes, alpha=24, beta=12, variant='joint', controller_mask=False, compute_length=False):
    return rewrite(parent.build(codes, alpha, beta, variant, controller_mask, compute_length))


def polynomial_source(packet):
    return parent.polynomial_source(packet)


def degree_top(packet, w):
    expanded = dict(w)
    # Fixed hats equal one, so their degree-one homogeneous parts vanish.
    expanded.update({n:0 for n in packet['frozen_idle_coordinates']})
    return parent.degree_top(packet, expanded)


def source_checks():
    rng = random.Random(2643504)
    examples = [(), ((1,),), ((1, 2),), ((1,), (2,)), ((1, 2, 3),),
        ((1, 2), (3, 4)), ((1, 2, 3, 4, 5, 6, 7, 8, 1, 2),),
        (tuple(1+i%8 for i in range(14)),), (tuple(1+i%8 for i in range(16)),),
        ((1,), (2, 3, 4), (5,), (6, 7, 8), (1, 2))]
    records, cases, signed, exemplar = [], 0, 0, None
    for codes in examples:
      for variant in ('four', 'six', 'shifted', 'strong', 'joint'):
       for reuse in (False, True):
        if reuse and parent.build(codes)['m'] < 8:
            continue
        for comp in (False, True):
            old = parent.build(codes, variant=variant, controller_mask=reuse, compute_length=comp)
            packet = rewrite(old)
            source, out = polynomial_source(packet)
            prior, prior_out = parent.polynomial_source(old)
            assert packet['comparisons'] == old['comparisons']
            assert packet['positive_witnesses'] == old['positive_witnesses']-packet['frozen_idle_count']
            assert len(source) == len(prior)-packet['frozen_idle_saving']['operations']
            for case in range(24):
                positive = case < 16
                z = {n:rng.randrange(1, 6) if positive else rng.randrange(-3, 4)
                     for n in packet['parameters']+packet['auxiliaries']}
                restored = dict(z)
                restored.update({n:1 for n in packet['frozen_idle_coordinates']})
                env, before = execute(source, z), execute(prior, restored)
                changed = set(packet['frozen_idle_changed_registers'])
                assert all(env[n] == before[n] for n, _, _, _ in source if n in before and n not in changed)
                assert residuals(packet, env) == residuals(old, before)
                assert env[out] == before[prior_out]
                for n in changed:
                    assert before[n]-env[n] == packet['frozen_idle_count']
                P = env['controller__geometry_power'] if comp else z['P']
                a, m = packet['active_edges'], packet['m']
                direct = sum((z[f'controller__edge_hat{i}']-1)*P**i for i in range(a))
                assert env['controller__edge_word'] == direct
                assert env['computed_J'] == sum(z[f'controller__edge_hat{i}']-1 for i in range(a))
                if packet['frozen_idle_count']:
                    for plan in packet['frozen_idle_pack_plans']:
                        outputs = {row[0] for row in plan['source']}
                        probe = execute(plan['source'], {n:v for n,v in before.items() if n not in outputs})
                        assert probe['controller__edge_word'] == direct
                cases += 1
                signed += not positive
            weights = {n:1+i%3 for i,n in enumerate(packet['parameters']+packet['auxiliaries'])}
            weights['selection__tau_gap'] = 1
            for i in range(packet['active_edges']):
                weights[f'controller__edge_hat{i}'] = 1 << i
            degree, top = degree_top(packet, weights)[:2]
            assert top != 0
            pc = Counter('M' if op == '*' else 'A' for _,op,_,_ in source)
            records.append(dict(codes=codes, m=packet['m'], active_edges=packet['active_edges'],
                padding=packet['frozen_idle_count'], variant=variant, controller_mask=reuse,
                compute_length=comp, plan=packet['frozen_idle_plan'], saving=packet['frozen_idle_saving'],
                certificate_operations=packet['operations'], polynomial_operations=len(source),
                polynomial_M=pc['M'], polynomial_A=pc['A'], equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'], exact_degree=degree))
            if codes == examples[6] and variant == 'joint' and reuse and comp:
                exemplar = dict(packet, polynomial_finalizer=source[packet['operations']:], polynomial_output=out)
                assert (packet['operations'],len(source),pc['M'],pc['A'],degree,packet['positive_witnesses']) == (247,264,113,151,3504,37)
    return dict(records=records, source_example=exemplar,
                exact_parent_specialization_cases=cases, signed_cases=signed)


def path_checks():
    rng = random.Random(264111)
    cases = relabeled = 0
    for codes in ((), ((1, 2),), ((1,), (2, 3, 4)), ((1,2,3,4,5,6,7,8,1,2),)):
        packet = build(codes)
        active, m = packet['active_edges'], packet['m']
        paths, start = [], 1
        for code in codes:
            paths.append(tuple(range(start, start+len(code))))
            start += len(code)
        for _ in range(64):
            edges = []
            for _ in range(rng.randrange(1, 12)):
                if not paths or rng.randrange(2):
                    edges.append(rng.choice([0]+list(range(active,m))))
                else:
                    edges.extend(rng.choice(paths))
            new = [0 if e >= active else e for e in edges]
            assert [packet['edges'][e] for e in edges] == [packet['edges'][e] for e in new]
            state = 0
            for e in new:
                a,b,_ = packet['edges'][e]
                assert a == state
                state = b
            assert state == 0 and all(e < active for e in new)
            B = 1 << max(5, m.bit_length()+1)
            P = B**len(new); J = (P-1)//(B-1)
            fields = [sum(B**j for j,e in enumerate(new) if e == i) for i in range(m)]
            assert all(v == 0 for v in fields[active:]) and sum(fields) == J
            mask = J*sum(P**i for i in range(m))
            word = sum(v*P**i for i,v in enumerate(fields))
            assert word & mask == word
            cases += 1
            relabeled += sum(a != b for a,b in zip(edges,new))
    return dict(path_normalizations=cases, padded_idle_occurrences_replaced=relabeled,
                scope='Actual path and scalar subset fixtures; positive native Pell extensions follow from the inherited AND converse, not from these finite checks.')


def verify():
    sources = source_checks()
    # General elementary ledger inequality; this is supplementary to its proof.
    ledger_cases = 0
    for h in range(1,13):
        m = 1 << h
        for a in range(m//2+1 if h > 1 else 1, m):
            k = m-a
            r = repunit_cost(k)
            tail = 3*k-2-r['M']-r['A']+int(k == 1)
            assert tail >= 2*k
            ledger_cases += 1
    return dict(status='PASS_GROUP_PROJECTIVE_FROZEN_IDLE_PADDING', **sources,
                normalized_paths=path_checks(), elementary_tail_saving_cases=ledger_cases,
                scope='Exact arbitrary-integer parent specialization and unchanged accepted positive input relation. Padding selectors are fixed to zero; native m-lane scale and masks remain paid. No parent-tuple bijection or numerical universal alphabet is asserted.')


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
