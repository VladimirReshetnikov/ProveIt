"""Share exact arithmetic in the complete four-tile tag history.

Five multiplications and two additions are removed. Every comparison
residual and the complete output polynomial are unchanged over integers.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_population_projection389 as parent
import native_binary_input_dilation_unit179 as ordering

compiler = parent.compiler


def rewrite_rows(old, prefix='hist__'):
    """Guard the literal H161 history; accept compatible full-source successors."""
    n = lambda name: prefix+name
    P2 = n('P2__51')
    expected = {
        'P2__51': ('*', 'P__10', 'P__10'),
        'P3__78': ('*', 'P2__51', 'P__10'),
        'P6__80': ('*', 'P3__78', 'P3__78'),
        'P7__81': ('*', 'P6__80', 'P__10'),
        'P4__84': ('*', 'P2__51', 'P2__51'),
        'P8__85': ('*', 'P4__84', 'P4__84'),
        'P9__86': ('*', 'P8__85', 'P__10'),
        'P5__97': ('*', 'P4__84', 'P__10'),
        'P10__98': ('*', 'P5__97', 'P5__97'),
        'P11__99': ('*', 'P10__98', 'P__10'),
        'repunit_factor__50': ('+', 'P__10', 1),
        'range_second_history__56': ('*', 'H_V', 'P__10'),
        'range_histories__57': ('+', 'H_U', 'range_second_history__56'),
        'V_repeated__66': ('*', 'H_V', 'repunit_factor__50'),
        'V_region__67': ('*', 'P__10', 'V_repeated__66'),
        'history_batch__68': ('+', 'H_U', 'V_region__67'),
        'selector_sum__4': ('+', 'Shat0', 'Shat1'),
        'selector_sum__5': ('+', 'Shat2', 'selector_sum__4'),
        'selector_sum__6': ('+', 'Shat3', 'selector_sum__5'),
        'J__7': ('-', 'selector_sum__6', 4),
        'group_sum__58': ('+', 'Shat1', 'Shat2'),
        'linear_group__164': ('+', 'Shat0', 'Shat3'),
    }
    alias = lambda value: n(value) if isinstance(value, str) else value
    rows = {name: (op, a, b) for name, op, a, b in old['source']}
    assert len(rows) == len(old['source'])
    for name, (op, a, b) in expected.items():
        assert rows[n(name)] == (op, alias(a), alias(b)), name
    consumers = {
        'P4__84': {'P8__85', 'P5__97'}, 'P8__85': {'P9__86'},
        'P5__97': {'P10__98'}, 'P10__98': {'P11__99'},
        'V_repeated__66': {'V_region__67'}, 'V_region__67': {'history_batch__68'},
        'selector_sum__4': {'selector_sum__5'}, 'selector_sum__5': {'selector_sum__6'},
    }
    exported = set(old.get('interfaces', {}).values()) | set(old.get('public_registers', {}).values())
    for private, allowed in consumers.items():
        actual = {name for name, _, a, b in old['source'] if n(private) in (a, b)}
        assert actual == {n(name) for name in allowed}, (private, actual)
        assert not any(n(private) in pair for pair in old['comparisons'])
        assert n(private) not in exported
    deleted = {n(name) for name in ('P4__84', 'P8__85', 'P5__97', 'P10__98',
                                   'V_repeated__66', 'selector_sum__4', 'selector_sum__5')}
    changes = {
        n('P9__86'): ('*', n('P7__81'), P2),
        n('P11__99'): ('*', n('P9__86'), P2),
        n('V_region__67'): ('*', P2, n('H_V')),
        n('history_batch__68'): ('+', n('range_histories__57'), n('V_region__67')),
        n('selector_sum__6'): ('+', n('group_sum__58'), n('linear_group__164')),
    }
    source = [(name, *changes.get(name, (op, a, b)))
              for name, op, a, b in old['source'] if name not in deleted]
    source = ordering.sort_source(source, old['parameters']+old['auxiliaries'])
    assert len(source) == len(old['source'])-7
    old_counts, new_counts = (Counter(op for _, op, _, _ in s) for s in (old['source'], source))
    assert new_counts['*'] == old_counts['*']-5
    assert new_counts['+']+new_counts['-'] == old_counts['+']+old_counts['-']-2
    return source, deleted, {n('V_region__67')}


def rewrite_history(old):
    assert old['layout'] == 'slope_classes' and old['tiles'] == 4
    assert old['scale_exponent'] == 11 and old['selected_products'] == 3
    source, deleted, changed = rewrite_rows(old, '')
    packet = dict(old, source=source, shared_history_arithmetic=True,
                  arithmetic_deleted_registers=sorted(deleted),
                  arithmetic_changed_private_registers=sorted(changed))
    compiler.recount(packet)
    if 'wrapper_operations' in old:
        packet['wrapper_operations'] = old['wrapper_operations']-7
    if 'positive_witnesses' in old:
        packet['positive_witnesses'] = packet['witnesses']
    assert packet['operations'] == old['operations']-7
    return packet


def rewrite(old):
    """Exact full-source rewrite; it does not assume the parent has cost389."""
    source, deleted, changed = rewrite_rows(old)
    history = rewrite_history(old['history_packet'])
    packet = dict(old, source=source, history_packet=history,
                  shared_history_arithmetic=True, arithmetic_parent=old,
                  arithmetic_deleted_registers=sorted(deleted),
                  arithmetic_changed_private_registers=sorted(changed))
    compiler.recount(packet)
    compiler.check_source(packet)
    assert packet['comparisons'] == old['comparisons']
    assert packet['parameters'] == old['parameters'] and packet['auxiliaries'] == old['auxiliaries']
    assert packet['operations'] == old['operations']-7
    return packet


def build(form='normalized', *, merge_bound=True, project_J=True, project_Ahat=True):
    return rewrite(parent.build(form, merge_bound=merge_bound,
                                project_J=project_J, project_Ahat=project_Ahat))


def ledger(packet):
    source, out = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    old = packet['arithmetic_parent']
    oldsource, _ = compiler.parent.polynomial_source(old)
    oldcounts = Counter('M' if op == '*' else 'A' for _, op, _, _ in oldsource)
    assert len(source) == len(oldsource)-7
    assert counts['M'] == oldcounts['M']-5 and counts['A'] == oldcounts['A']-2
    return dict(form=packet['form'], bound_is_program_E=packet['bound_is_program_E'],
        project_J=packet['project_J'], project_Ahat=packet['project_Ahat'],
        certificate={k: packet[k] for k in ('operations', 'multiplications',
                     'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=out),
        history_operations=packet['history_packet']['operations'],
        **parent.degree_bound(packet))


def verify():
    rng = random.Random(382184198)
    records, cases, signed = [], 0, 0
    for form in ('raw', 'units', 'normalized'):
        for merge in (False, True):
            for Jp, Ap in ((False, False), (False, True), (True, False), (True, True)):
                old = parent.build(form, merge_bound=merge, project_J=Jp, project_Ahat=Ap)
                packet = rewrite(old)
                records.append(ledger(packet))
                source, output = compiler.parent.polynomial_source(packet)
                oldsource, oldout = compiler.parent.polynomial_source(old)
                for case in range(24):
                    C = {name: rng.randrange(-5, 6) for name in compiler.NUMERALS}
                    values = {name: rng.randrange(1, 5) if case < 12 else rng.randrange(-3, 4)
                              for name in packet['parameters']+packet['auxiliaries']}
                    before = compiler.parent.execute(compiler.materialize(oldsource, C), values)
                    after = compiler.parent.execute(compiler.materialize(source, C), values)
                    assert after[output] == before[oldout]
                    get = compiler.parent.scalar
                    assert [get(a, after)-get(b, after) for a, b in packet['comparisons']] == [
                        get(a, before)-get(b, before) for a, b in old['comparisons']]
                    assert all(after[name] == before[name] for name, _, _, _ in packet['source']
                               if name not in packet['arithmetic_changed_private_registers'])
                    assert all(after[name] == before[name] for name in packet.get('unit_factors', []))
                    cases += 1
                    signed += case >= 12
    # Independently stated polynomial identities at degenerate signed bases too.
    local_cases = 0
    for P in (-7, -2, -1, 0, 1, 2, 3, 11):
        for _ in range(32):
            H, V, a, b, c, d = [rng.randrange(-11, 12) for _ in range(6)]
            assert (P**7*P**2, (P**7*P**2)*P**2) == (P**9, P**11)
            assert H+P*((P+1)*V) == (H+P*V)+P**2*V
            assert d+(c+(a+b)) == (b+c)+(a+d)
            local_cases += 1
    # Genuine positive outer histories use the same scalar mask words and
    # transport residuals; placeholder native coordinates are not Pell zeros.
    import binary_tag_four_tile_history as tag
    import pcp_affine_slope_class_history as selected
    history = tag.build()['raw_packet']['history_packet']
    short = rewrite_history(history)
    assert (history['operations'], short['operations']) == (161, 154)
    paths = 0
    for length in range(1, 7):
        for _ in range(12):
            word = tuple(rng.randrange(4) for _ in range(length))
            values = selected.positive_outer_fixture(history, word, rng.randrange(1, 6))
            before = compiler.parent.execute(history['source'], values)
            after = compiler.parent.execute(short['source'], values)
            for key in ('P', 'S', 'Mc', 'T', 'Hb', 'Mb', 'Zb', 'Gpack', 'RM', 'H', 'M', 'Z', 'scale', 'nextU', 'nextV'):
                assert before[history['interfaces'][key]] == after[short['interfaces'][key]]
            assert all(after[a] == after[b] for a, b in short['comparisons'][:3])
            H, M, Z = (after[short['interfaces'][key]] for key in ('H', 'M', 'Z'))
            assert H & M == Z
            paths += 1
    # Guard failures cover extra consumers, changed powers and repeated application.
    old = parent.build()
    bad = [dict(old, source=old['source']+[('private_power_leak', '+', 'hist__P4__84', 1)]),
           dict(old, comparisons=old['comparisons']+[('hist__V_region__67', 1)]),
           dict(old, source=[(n, '*', 'hist__P3__78', 'hist__P__10') if n == 'hist__P4__84'
                             else (n, op, a, b) for n, op, a, b in old['source']]),
           rewrite(old)]
    for broken in bad:
        try:
            rewrite(broken)
        except (AssertionError, KeyError):
            pass
        else:
            raise AssertionError('invalid private source contract accepted')
    packet = build()
    source, out = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(source)
    assert ledger(packet)['polynomial'] == dict(operations=382, multiplications=184,
        additions_subtractions=198, output=out)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_SHARED_HISTORY382', ledgers=records,
        whole_certificate_residual_output_identities=cases, signed_cases=signed,
        separately_stated_local_identities=local_cases, genuine_positive_outer_paths=paths,
        rejected_private_contracts=len(bad), fixed_recipe=parent.parent.parent.u9.components()[-1],
        source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
        example=dict(source=encoded, output=out, comparisons=packet['comparisons'],
                     parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                     fixed_numeral_definitions=compiler.NUMERALS),
        scope='The complete four-tile history saves5M2A by exact integer identities. '
              'The default literal U9 polynomial costs382=184M198A with67 positive '
              'witnesses,22 comparisons,four program parameters and degree at most2241. '
              'All old residuals and the full polynomial are unchanged; no relaxed '
              'counter, selected-history predicate, or positive-domain projection is used.')


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
    print(result['ledgers'][-1])
