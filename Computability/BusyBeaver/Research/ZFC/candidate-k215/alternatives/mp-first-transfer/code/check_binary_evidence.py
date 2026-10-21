#!/usr/bin/env python3
"""Portable checks of binary research evidence; Python standard library only.

verify() is deterministic and writes nothing. The command line prints JSON,
and optionally writes an explicit --out path. These checks establish exact
finite graph/trace facts, not a proof-assistant formalization or a state bound.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('Assertions must be enabled: do not use python -O.')

ROOT = Path(__file__).resolve().parents[1]
CANDIDATE_SHA256 = '485ca26885508bdaf76ecd8f46827b64518ca1d9e32de81b2a8ac2904a49d9f2'
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_json(path):
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == '.gz' else raw)


def parse(raw):
    table, starts = {}, []
    for line in raw.decode('ascii').splitlines():
        line = line.strip()
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
            continue
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in table
        table[q, b] = w, 1 if d == 'R' else -1, z
    states = {q for q, b in table}
    assert len(starts) == 1 and starts[0] in states
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    halts = {z for w, d, z in table.values()} - states
    assert len(halts) == 1
    return table, starts[0], next(iter(halts))


def graph(raw, reflect=False):
    table, initial, halt = parse(raw)
    order, rename = [initial], {initial: 0}
    for q in order:
        for b in (0, 1):
            z = table[q, b][2]
            if z != halt and z not in rename:
                rename[z] = len(rename)
                order.append(z)
    rows = []
    for q in order:
        for b in (0, 1):
            w, d, z = table[q, b]
            rows.append([rename[q], b, w, -d if reflect else d,
                         -1 if z == halt else rename[z]])
    return rows, {
        'working_states': len(table) // 2,
        'graph_reachable_states': len(order),
        'one_writing_rows': sum(w for w, d, z in table.values()),
        'left_rows': sum(d == -1 for w, d, z in table.values()),
        'canonical_sha256': sha(json.dumps(rows, separators=(',', ':')).encode()),
    }


def check_graphs(root):
    raw = (root / 'machine/t215.native.tm').read_bytes()
    assert sha(raw) == CANDIDATE_SHA256
    candidate, facts = graph(raw)
    assert facts['working_states'] == facts['graph_reachable_states'] == 215
    manifest_path = root / 'research/comparison-tables/manifest.json'
    manifest = read_json(manifest_path)
    assert manifest['repository_commit'] == 'ead95b5b336818a53c89b8c3d5249822e0570939'
    assert sha((root / 'machine/sites215.json').read_bytes()) == manifest['candidate_source_sha256']
    raw_hashes, graph_hashes, reachable = set(), set(), set()
    for item in manifest['tables']:
        other_raw = (root / item['file']).read_bytes()
        assert sha(other_raw) == item['raw_sha256']
        assert item['raw_sha256'] not in raw_hashes
        raw_hashes.add(item['raw_sha256'])
        other, other_facts = graph(other_raw)
        reflected, reflected_facts = graph(other_raw, reflect=True)
        assert other_facts['working_states'] == 215
        for key, value in other_facts.items():
            assert item[key] == value
        assert item['reflection_sha256'] == reflected_facts['canonical_sha256']
        assert other != candidate and reflected != candidate
        assert item['isomorphic'] is False and item['isomorphic_after_reflection'] is False
        graph_hashes.add(other_facts['canonical_sha256'])
        reachable.add(other_facts['graph_reachable_states'])
    assert len(raw_hashes) == 47 and len(graph_hashes) == 23
    return {
        'status': 'EXACT_ROOTED_GRAPH_DISTINCTNESS_PASS',
        'candidate_table_sha256': sha(raw),
        'candidate_source_sha256': manifest['candidate_source_sha256'],
        'candidate': facts,
        'unique_raw_comparison_tables': len(raw_hashes),
        'unique_rooted_comparison_graphs': len(graph_hashes),
        'comparison_reachable_state_counts': sorted(reachable),
        'provenance_manifest_sha256': sha(manifest_path.read_bytes()),
        'scope': 'Read/write/direction-labelled rooted graph isomorphism, with arbitrary state renaming and optional global tape reflection. Candidate has all 215 states graph-reachable. No claim of exhaustive historical novelty or semantic inequivalence.',
    }


def replay(table, initial, head, ones, trace):
    ones = set(ones)
    q = initial
    for row in trace:
        assert len(row) == 6
        a, position, b, w, d, z = row
        assert (a, position, b) == (q, head, int(head in ones))
        assert table[q, b] == (w, d, z)
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        q, head = z, head + d
    return q, head, ones


def outward_ray(table, q, head, ones):
    assert head not in ones
    w, d, z = table[q, 0]
    assert z == q
    assert not ones or (d == 1 and head > max(ones)) or (d == -1 and head < min(ones))
    return w, d


def effective_bytes(table):
    return ('#! start 74\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
        for (q, b), (w, d, z) in sorted(table.items()))).encode()


def check_obstructions(root):
    directory = root / 'research/negative-controls'
    raw = (directory / 'runtime214-zero.native.tm').read_bytes()
    base, initial, halt = parse(raw)
    states = {q for q, b in base}
    assert len(states) == 214 and halt == 254
    assert base[198, 0] == (0, -1, 40)
    assert base[51, 0] == (0, 1, 122) and base[88, 0] == (0, -1, 51)
    assert 301 not in states
    reports = []
    for append, name in ((0, 'all-start-proof'), (1, 'all-start-append1-proof')):
        table = dict(base)
        table[198, 0] = append, -1, 40
        certificate = read_json(directory / (name + '.json.gz'))
        assert certificate['input_table_sha256'] == sha(raw)
        assert certificate['effective_table_sha256'] == sha(effective_bytes(table))
        assert certificate['append_value'] == append
        entries = {q for q in states if table[q, 0][0] == 1}
        assert set(certificate['first_write_states']) == entries
        roots = certificate['zero_prefix_classification']
        assert {int(k) for k in roots} == states
        zero_cycles = 0
        for key, rec in roots.items():
            start = int(key)
            trace = rec['zero_prefix']
            assert all(row[2] == row[3] == 0 for row in trace)
            assert len({row[0] for row in trace}) == len(trace)
            assert all(row[0] not in entries for row in trace)
            q, head, ones = replay(table, start, 0, set(), trace)
            assert not ones
            assert (q, head) == (rec['end_state'], rec['end_head'])
            if rec['class'] == 'FIRST_WRITE':
                assert q in entries and rec['cycle_start'] is None
            else:
                assert rec['class'] == 'ZERO_ONLY_CYCLE'
                index = rec['cycle_start']
                assert isinstance(index, int) and 0 <= index < len(trace)
                assert trace[index][0] == q and q not in entries
                zero_cycles += 1
        ray_certificates = certificate['first_write_ray_certificates']
        assert {int(k) for k in ray_certificates} == entries
        maximum = 0
        for key, rec in ray_certificates.items():
            q, head, ones = replay(table, int(key), 0, set(), rec['trace'])
            assert len(rec['trace']) == rec['steps']
            assert (q, head, sorted(ones)) == (rec['state'], rec['head'], rec['one_cells'])
            w, d = outward_ray(table, q, head, ones)
            assert (w, d) == (rec['write'], rec['direction'])
            maximum = max(maximum, rec['steps'])
        reports.append({'append': append, 'initial_states': len(states),
                        'zero_only_cycle_initial_states': zero_cycles,
                        'first_write_states': sorted(entries),
                        'maximum_first_write_to_ray_steps': maximum,
                        'effective_table_sha256': sha(effective_bytes(table))})
    certificate = read_json(directory / 'onebit-proof.json.gz')
    assert certificate['input_table_sha256'] == sha(raw)
    seen, counts, maximum = set(), {0: {'RAY': 0, 'HALT': 0}, 1: {'RAY': 0, 'HALT': 0}}, 0
    for rec in certificate['cases']:
        key = rec['append'], rec['start'], rec['initial_head']
        assert key not in seen
        seen.add(key)
        append, start, head = key
        assert append in (0, 1) and start in states and head in (-1, 1)
        table = dict(base)
        table[198, 0] = append, -1, 40
        q, head, ones = replay(table, start, head, {0}, rec['trace'])
        assert len(rec['trace']) == rec['steps']
        assert (q, head, sorted(ones)) == (rec['state'], rec['head'], rec['ones'])
        if rec['status'] == 'HALT':
            assert q == halt
        else:
            assert rec['status'] == 'RAY'
            outward_ray(table, q, head, ones)
        counts[append][rec['status']] += 1
        maximum = max(maximum, rec['steps'])
    assert seen == {(a, q, h) for a in (0, 1) for q in states for h in (-1, 1)}
    assert all(value == {'RAY': 427, 'HALT': 1} for value in counts.values())
    assert maximum == certificate['maximum_steps'] == 379
    return {
        'status': 'EXACT_BLANK_AND_ONE_BIT_CLASSIFICATIONS_PASS',
        'runtime214_input_sha256': sha(raw),
        'all_start_variants': reports,
        'one_bit_cases': len(seen),
        'one_bit_counts': counts,
        'maximum_one_bit_steps': maximum,
        'scope': 'Only this 214-state runtime-fold core and the two values of row 198/0. Every old initial state diverges on blank tape. Every one-bit entry either halts explicitly or reaches an outward ray. Consequently one newly added initial state with unchanged existing rows has only these outcomes: its zero transition enters an old state with blank or one-bit tape, or self-loops outwards. This classifies those initializers; it is not a general 214-state lower bound.',
    }


def frame(pc, logical, spares, gap):
    physical = [0] * 9
    for i, position in enumerate(PHY):
        physical[position] = logical[i]
    ones = {-1, 64 + gap} | {i for i, bit in enumerate(pc) if bit == '1'}
    position = 65 + gap
    for value in physical + list(spares):
        position += 1
        ones.update(range(position, position + value + 1))
        position += value + 1
    return ones


def check_negative_control(root):
    directory = root / 'research/negative-controls'
    raw = (directory / 'simple35-permuted-invalid.native.tm').read_bytes()
    source_raw = (directory / 'simple35-permuted-invalid.sites.json').read_bytes()
    rec = read_json(directory / 'simple35-counterexample.json')
    assert sha(raw) == rec['table_sha256'] and sha(source_raw) == rec['source_sha256']
    assert json.loads(source_raw)[rec['site_index']] == rec['site']
    table, initial, halt = parse(raw)
    assert len(table) == 430
    pc, op, arg = rec['site']
    assert op == 'CD' and rec['registers'][arg] == 0
    ones = frame(pc, rec['registers'], rec['spares'], rec['gap'])
    assert sorted(ones) == rec['initial_ones']
    for i, row in enumerate(rec['trace']):
        assert row[0] == i
    q, head, ones = replay(table, 84, 0, ones, [row[1:] for row in rec['trace']])
    assert len(rec['trace']) == rec['steps'] == 634
    assert (q, head, sorted(ones)) == (rec['actual']['state'], rec['actual']['head'], rec['actual']['ones'])
    stripped = pc[:pc.rindex('0')]
    value = int(stripped, 2) + 1
    assert value < 2 ** len(stripped)
    successor = format(value, '0' + str(len(stripped)) + 'b')
    expected = frame(successor, rec['registers'], rec['spares'], rec['gap'])
    assert rec['expected'] == {'state': 84, 'head': 0, 'ones': sorted(expected)}
    assert (q, head, ones) != (84, 0, expected)
    return {
        'status': 'CONCRETE_INVALID_ALLOCATION_COUNTEREXAMPLE_REPLAYED',
        'table_sha256': sha(raw), 'source_sha256': sha(source_raw),
        'site_index': rec['site_index'], 'site': rec['site'],
        'logical_registers': rec['registers'], 'spares': rec['spares'],
        'steps': rec['steps'], 'expected_successor': successor,
        'scope': 'The abstract 35-leaf command is not refuted; this particular decoder allocation fails at a legitimate whole-tape primitive frame.',
    }


def check_search_receipts(root):
    directory = root / 'research/bounded-fold-search'
    items = []
    expected_counts = {'permuted': 629160, 'simple': 625736,
                       'simple-permuted': 625736, 'context-root': 620600}
    for tag, count in expected_counts.items():
        rec = read_json(directory / tag / 'result.json')
        assert sha((directory / tag / 'seed.native.tm').read_bytes()) == rec['seed_sha256']
        assert rec['status'] == 'COMPLETE_BOUNDED_SEARCH' and rec['hits'] == []
        assert (rec['radius'], rec['fuel'], rec['pair_count'], rec['candidate_count']) == (5, 97, 46010, count)
        items.append({'seed': tag, 'seed_sha256': rec['seed_sha256'],
                      'candidate_count': count,
                      'ordered_rejections_sha256': rec['ordered_rejections_sha256']})
    return {'status': 'RECEIPT_BINDING_PASS_SEARCH_NOT_RERUN',
            'total_recorded_specs': sum(expected_counts.values()), 'seeds': items,
            'scope': 'Only hashes and report structure are checked here. Optional run_search.py reruns each finite-window search. A failed search does not establish minimality.'}


def verify():
    return {'status': 'BINARY_RESEARCH_EVIDENCE_PASS',
            'graph_comparisons': check_graphs(ROOT),
            'startup_obstructions': check_obstructions(ROOT),
            'invalid_allocation_negative_control': check_negative_control(ROOT),
            'bounded_search_receipts': check_search_receipts(ROOT)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path)
    args = parser.parse_args()
    report = verify()
    text = json.dumps(report, indent=2, sort_keys=True) + '\n'
    if args.out:
        args.out.write_text(text)
    print(text, end='')


if __name__ == '__main__':
    main()
