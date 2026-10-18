#!/usr/bin/env python3
"""Finite d=181 return-contract failures for shortened zero-run detectors.

This checks one exact prepared instruction at the known bootstrap distance,
with 167 value-one spares. It makes no blank-run or eventual-halting claim.
The whole support, state and head are checked by two literal interpreters.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
from probe_state204_safe_phase import TABLE_SHA256, PROGRAM_SHA256
from probe_state204_safe_phase import table, paint, dense_verify
from source_phase_certificate import increment, strip

PC = '111010010010000000'
LOGICAL = [3, 0, 0, 0, 0, 0, 0, 0, 0]
GAP, SPARES = 181, [1] * 167
EXPECTED_PC = increment(strip(PC, '0', 1))


def check_source_site(path):
    src = path.read_text().split('Definition p254_tab', 1)[1]
    src = src.split('[', 1)[1].split('].', 1)[0]
    op = r'(?:CN|CI|CD|CB|CC) \d+|CH'
    tree = re.findall(r'\((' + op + r'),\s*(' + op + r')\)', src)
    assert len(tree) == 6459
    node = 0
    for depth, bit in enumerate(PC, 1):
        edge = tree[node][int(bit)].split()
        if edge[0] != 'CN':
            assert depth == len(PC) and edge == ['CD', '1']
            return
        node = int(edge[1])
    raise AssertionError('PC does not end at the claimed CD1 source site')


def replay(t, label, changed_source=None):
    ones = paint(PC, LOGICAL, SPARES, GAP)
    expected = paint(EXPECTED_PC, LOGICAL, SPARES, GAP)
    initial = sorted(ones)
    q, h = 96, 0
    dispatches, changed_visits = [], []
    for steps in range(1, 10001):
        key = q, int(h in ones)
        if key == (changed_source, 0):
            changed_visits.append({'steps_before': steps - 1,
                'head': h, 'local_support_minus1_to30': sorted(
                    p for p in ones if -1 <= p <= 30)})
        w, d, q = t[key]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
        assert q != 254
        if q == 96:
            exact = h == 0 and ones == expected
            dispatches.append({'steps': steps, 'head': h,
                               'exact_expected_endpoint': exact})
            if exact:
                status = 'EXACT_EXPECTED_ENDPOINT'
                break
            if h != 0:
                status = 'FIRST_FALSE_DISPATCHER_ORIGIN'
                break
    else:
        raise AssertionError('Certificate endpoint not reached')
    result = {'label': label, 'status': status, 'steps': steps,
        'state': q, 'head': h, 'initial_pc': PC,
        'expected_pc': EXPECTED_PC, 'initial_logical': LOGICAL,
        'gap': GAP, 'spare_values': SPARES,
        'dispatches': dispatches, 'changed_visits': changed_visits,
        'initial_ones': initial, 'final_ones': sorted(ones),
        'expected_ones': sorted(expected)}
    result['independent_dense'] = dense_verify(t, result)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--program', type=Path, required=True)
    ap.add_argument('--output', type=Path, default=Path('short_detector_d181.json'))
    args = ap.parse_args()
    assert hashlib.sha256(args.table.read_bytes()).hexdigest() == TABLE_SHA256
    assert hashlib.sha256(args.program.read_bytes()).hexdigest() == PROGRAM_SHA256
    check_source_site(args.program)
    base = table(args.table)
    baseline = replay(base, 'context246')
    assert (baseline['status'], baseline['steps'], baseline['head']) == (
        'EXACT_EXPECTED_ENDPOINT', 1514, 0)
    assert [x['steps'] for x in baseline['dispatches']] == [386, 782, 1514]
    assert all(x['head'] == 0 for x in baseline['dispatches'])
    counterexamples = []
    for n, deleted, source, steps, before in [
            (245, [74], 58, 749, 747),
            (244, [58, 74], 41, 355, 353)]:
        t = {k: v for k, v in base.items() if k[0] not in deleted}
        t[source, 0] = (0, -1, 84)
        assert len(t) == 2 * n
        assert all(r not in deleted for w, d, r in t.values())
        result = replay(t, str(n) + '_shortened_detector', source)
        assert (result['status'], result['steps'], result['head']) == (
            'FIRST_FALSE_DISPATCHER_ORIGIN', steps, 11)
        trigger = result['changed_visits'][-1]
        assert (trigger['steps_before'], trigger['head']) == (before, 11)
        support = set(trigger['local_support_minus1_to30'])
        right_one = 19 if n == 245 else 18
        assert 10 in support and right_one in support
        assert not any(p in support for p in range(11, right_one))
        result['deleted_states'] = deleted
        result['replacement_row'] = [source, 0, 0, 'L', 84]
        result['internal_word'] = {'start': 10, 'end': right_one,
                                  'word': '1' + '0' * (right_one - 11) + '1'}
        counterexamples.append(result)
    result = {'status': 'PREPARED_RETURN_CONTRACT_OBSTRUCTIONS_VERIFIED',
        'blank_reachability_proved': False,
        'eventual_mutant_behavior_claimed': False,
        'table_sha256': TABLE_SHA256, 'program_sha256': PROGRAM_SHA256,
        'baseline': baseline, 'counterexamples': counterexamples}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'output': str(args.output),
        'baseline_exact_steps': 1514, 'false_dispatcher_certificates': [
            {'states': 245, 'steps': 749, 'head': 11},
            {'states': 244, 'steps': 355, 'head': 11}]}, indent=2))


if __name__ == '__main__':
    main()
