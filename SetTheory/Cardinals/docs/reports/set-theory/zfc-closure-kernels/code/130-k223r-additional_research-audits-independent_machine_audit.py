#!/usr/bin/env python3
"""Second, read-only K223 audit; standard library, no construction imports.

The fold check uses finite truth tables to prove invariant consecution, then
checks the supplied positive traces against literal transitions on fixed
patches. Every unrepresented tape cell is arbitrary and must remain unread.
This is a universal local proof, not testing sampled executions.

The runtime section checks binding and engine identity, not a fresh universal
runtime proof. Run portable/reproduce.py for that separate fresh derivation.
"""
import argparse
import copy
import hashlib
import itertools
import json
from pathlib import Path
import zipfile


PINS = {
    'folds/parent226.k.tm': 'e7069fe4dc12fe62ba66cd88c27a51bfd83d548daad07591d3e0b0afaf6afe3d',
    'folds/candidate223.k.tm': '5bcee335bc5cf45b6ebc6d1f97a10e3cc8aae2af303b82c5cc9ce506a4d22ed7',
    'results/candidate223.tm': '0d4eb8ffbcd5dc025c8dac198c7d8a15404c35f63134b5e3ed0b7df7673d9231',
    'results/candidate223.legacy.tm': '2825e053950da9a6a6bbdd96ef5d96b680542fdf1d307973c553a18ed5baffe0',
    'results/sites.json': 'fe3713adaf008a71ba4fbc6433de760ef124b8638efbc5c75e3afa2c1142c24f',
    'results/runtime223_cases.json': 'a012f3aea9fad2010086c1613a36217b81f3c5cba4148e8545ac8ff64e3cb7da',
    'runtime/symbolic_runtime.py': 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
    'runtime/independent_runtime.py': '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
    'vendor/K224_Construction_2026-10-20.zip': 'cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887',
}


def demand(condition, reason):
    if not condition:
        raise ValueError(reason)


def read_json(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    start, rows = None, {}
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields:
            continue
        if fields[:2] == ['#!', 'start']:
            demand(start is None and len(fields) == 3, 'malformed start declaration')
            start = int(fields[2])
        elif not fields[0].startswith('#'):
            demand(len(fields) == 5, 'wrong transition arity')
            q, b, w, move, z = fields
            q, b, w, z = map(int, (q, b, w, z))
            demand(min(q, z) >= 0 and b in (0, 1) and w in (0, 1), 'invalid binary row')
            demand(move in ('L', 'R') and (q, b) not in rows, 'invalid/duplicate transition')
            rows[q, b] = (w, 1 if move == 'R' else -1, z)
    states = {q for q, b in rows}
    demand(start in states and set(rows) == set(itertools.product(states, (0, 1))), 'incomplete table')
    undefined = {z for w, d, z in rows.values()} - states
    demand(len(undefined) == 1, 'expected exactly one undefined halt state')
    return rows, start, undefined.pop()


def invariant_truth_tables(rows, supplied):
    """Exhaust all assignments to exactly the cells relevant to each row.

    Each tested assignment represents every infinite extension of that finite
    pattern. No reachability sampling is used: every enabled literal row is
    included, so initiation plus induction yields facts at every reachable
    old configuration on every initial tape.
    """
    states = {q for q, b in rows}
    facts = {q: {} for q in states}
    for q, bit_facts in supplied.items():
        q = int(q)
        demand(q in states, 'fact about absent state')
        facts[q] = {int(k): int(v) for k, v in bit_facts.items()}
        demand(all(v in (0, 1) for v in facts[q].values()), 'nonbinary fact')
    demand(not facts[0], 'facts constrain the initial tape')
    assignments, excluded = 0, []
    for (q, b), (w, d, z) in sorted(rows.items()):
        if 0 in facts[q] and facts[q][0] != b:
            excluded.append([q, b])
            continue
        fixed = dict(facts[q])
        fixed[0] = b
        targets = facts.get(z, {})
        free = sorted({k + d for k in targets} - set(fixed))
        for values in itertools.product((0, 1), repeat=len(free)):
            tape = {**fixed, **dict(zip(free, values))}
            tape[0] = w
            demand(all(tape[k + d] == v for k, v in targets.items()),
                   f'invariant counterexample via {q}/{b} to state {z}')
            assignments += 1
    return facts, {'local_assignments': assignments, 'excluded_rows': excluded}


def check_folds(parent, spec, certificate):
    current = dict(parent)
    demand(len(current) == 452 and len(spec['folds']) == 3, 'wrong fold chain size')
    demand(len(certificate['folds']) == 3, 'wrong number of block certificates')
    receipts = []
    for index, (fold, evidence) in enumerate(zip(spec['folds'], certificate['folds']), 1):
        facts, inductive = invariant_truth_tables(current, fold['invariant'])
        keep, drop = fold['keep'], fold['delete']
        demand(keep != drop and keep not in (0, 254) and drop not in (0, 254), 'invalid quotient')
        demand((keep, 0) in current and (drop, 0) in current, 'absent fold state')
        rename = lambda q: keep if q == drop else q
        new = {(q, b): (w, d, rename(z)) for (q, b), (w, d, z) in current.items() if q != drop}
        for b in (0, 1):
            w, d, z = fold['a' + str(b)]
            demand(w in (0, 1) and d in (-1, 1), 'invalid replacement row')
            new[keep, b] = (w, d, rename(z))
        working = {q for q, b in new}
        demand(set(new) == set(itertools.product(working, (0, 1))), 'incomplete transformed table')
        demand(all(z in working or z == 254 for w, d, z in new.values()), 'bad transformed target')
        needed = {(q, b) for q in (keep, drop) for b in (0, 1)
                  if 0 not in facts[q] or facts[q][0] == b}
        traces = evidence['positive_blocks']
        demand(len(traces) == len(needed), 'duplicate/missing block evidence')
        demand({(x['old_state'], x['read_bit']) for x in traces} == needed, 'block branch coverage')
        checked = []
        for item in traces:
            oldq, b = item['old_state'], item['read_bit']
            initial = {**facts[oldq], 0: b}
            patch = dict(initial)
            oldw, oldd, oldz = current[oldq, b]
            expected = {**initial, 0: oldw}
            q, h = keep, 0
            trace = item['trace']
            demand(len(trace) > 0, 'zero-step simulation is not permitted')
            for stated in trace:
                demand(q != 254 and h in patch, 'trace halts early or reads arbitrary exterior')
                write, move, nxt = new[q, patch[h]]
                demand(stated == [q, h, patch[h], write, move, nxt], 'trace differs from literal table')
                patch[h] = write
                q, h = nxt, h + move
            demand((q, h, patch) == (rename(oldz), oldd, expected), 'whole-tape endpoint mismatch')
            checked.append({'old_state': oldq, 'read': b, 'steps': len(trace),
                            'represented_cells': sorted(initial), 'endpoint': [q, h]})
        ordinary = 0
        for (q, b), (w, d, z) in current.items():
            if q not in (keep, drop):
                demand(new[rename(q), b] == (w, d, rename(z)), 'ordinary-row discrepancy')
                ordinary += 1
        receipts.append({'fold': index, 'keep': keep, 'delete': drop,
                         'old_states': len(current) // 2, 'new_states': len(new) // 2,
                         'invariant': inductive, 'ordinary_rows': ordinary, 'blocks': checked})
        current = new
    return current, receipts


def check_maps(root, kt, nt, lt):
    state_map = read_json(root / 'results/state_map.json')
    order, seen = [0], {0}
    for q in order:
        for b in (0, 1):
            z = kt[q, b][2]
            if z != 254 and z not in seen:
                order.append(z)
                seen.add(z)
    demand(seen == {q for q, b in kt}, 'graph-unreachable working state')
    expected = {q: i for i, q in enumerate(order)}
    expected[254] = len(order)
    for name, target, start, halt in [('k_to_canonical', nt, 0, 223), ('k_to_legacy', lt, 95, 254)]:
        mapping = {int(q): z for q, z in state_map[name].items()}
        demand(set(mapping) == seen | {254}, 'state map domain differs')
        demand(len(set(mapping.values())) == len(mapping), 'state map is not injective')
        demand(mapping[0] == start and mapping[254] == halt, 'mapped start/halt differs')
        demand({(mapping[q], b): (w, d, mapping[z]) for (q, b), (w, d, z) in kt.items()} == target,
               'literal relabeling discrepancy')
        if name == 'k_to_canonical':
            demand(mapping == expected, 'canonical ordering discrepancy')
        else:
            demand(mapping[84] == 96, 'legacy runtime dispatcher differs')
    demand(set(expected.values()) == set(range(224)), 'wrong canonical state count')
    return {'working_states': len(order), 'rows': len(kt), 'canonical_halt': 223,
            'canonical_dispatcher': expected[84], 'all_states_graph_reachable': True,
            'canonical_and_legacy_are_exact_bijections': True}


def check_bootstrap(root, canonical):
    """Execute the canonical table, independently of the build's K-label run."""
    q, head, support = 0, 0, set()
    for _ in range(409835):
        demand(q != 223, 'premature canonical halt')
        w, d, q = canonical[q, int(head in support)]
        if w:
            support.add(head)
        else:
            support.discard(head)
        head += d
    stored = read_json(root / 'results/bootstrap223.json')
    demand((q, head) == (22, -5), 'canonical blank endpoint differs')
    demand(sorted(support) == stored['one_cells'], 'full blank support differs')
    demand(stored['canonical_state'] == q and stored['head'] == head, 'stored endpoint differs')
    demand(min(support) == head - 1, 'unexpected left exterior')
    header = min(s for s in support if s >= head)
    cursor, blocks = header + 1, []
    while cursor <= max(support):
        demand(cursor not in support and cursor + 1 in support, 'malformed B block')
        count = 0
        cursor += 1
        while cursor in support:
            count += 1
            cursor += 1
        blocks.append(count - 1)
    logical = [blocks[j] for j in (6, 2, 0, 4, 3, 7, 8, 5, 1)]
    demand(logical == [3, 0, 0, 0, 3, 0, 0, 0, 0], 'initial logical registers differ')
    demand(blocks[9:] == [1] * 167 and header - head == 181, 'spare list/gap differs')
    demand(len(support) == 351, 'support cardinality differs')
    encoded = (json.dumps(sorted(support), separators=(',', ':')) + '\n').encode()
    return {'steps': 409835, 'canonical_state': q, 'head': head, 'logical_registers': logical,
            'one_cells': len(support), 'spare_count': 167, 'spare_value': 1,
            'header_distance': 181, 'whole_support_compact_json_sha256': hashlib.sha256(encoded).hexdigest(),
            'all_other_cells': 0}


def runtime_binding(root, lt):
    source = read_json(root / 'results/sites.json')
    addresses = {x[0] for x in source}
    demand(len(addresses) == len(source) == 4581, 'source leaf count/uniqueness differs')
    prefixes = {p[:i] for p in addresses for i in range(len(p))}
    demand(not addresses & prefixes and len(prefixes) == len(addresses) - 1, 'source prefix violation')
    demand(all(p + b in addresses | prefixes for p in prefixes for b in '01'), 'incomplete source tree')
    expected = [(i, b) for i, x in enumerate(source) for b in ((False, True) if x[1] == 'CD' else (False,))]
    cases = read_json(root / 'results/runtime223_cases.json')
    demand([(x['site_index'], x['positive']) for x in cases] == expected, 'runtime guard coverage differs')
    demand(len(cases) == 5956, 'wrong runtime case count')
    demand(all(len(x['duration']) == 13 and x['duration'][0] > 0 and
               all(type(c) is int and c >= 0 for c in x['duration']) for x in cases), 'invalid positive duration')
    receipt = read_json(root / 'results/runtime223.json')
    demand(sum(x['symbolic_steps'] for x in cases) == receipt['symbolic_steps'] == 1431799,
           'runtime symbolic census differs')
    demand(set(map(tuple, receipt['used_rows'])) == set(lt), 'stored runtime row coverage differs')
    for key, relative in [('source_sha256', 'results/sites.json'),
                          ('table_sha256', 'results/candidate223.legacy.tm'),
                          ('canonical_table_sha256', 'results/candidate223.tm'),
                          ('engine_sha256', 'runtime/symbolic_runtime.py'),
                          ('helper_sha256', 'runtime/independent_runtime.py'),
                          ('adapter_sha256', 'runtime223.py'),
                          ('cases_sha256', 'results/runtime223_cases.json')]:
        demand(receipt[key] == sha(root / relative), 'runtime receipt binding differs: ' + key)
    compared = []
    with zipfile.ZipFile(root / 'vendor/K224_Construction_2026-10-20.zip') as archive:
        for filename in ('symbolic_runtime.py', 'independent_runtime.py'):
            entries = [n for n in archive.namelist() if n.endswith('/machine/vendor/' + filename)]
            demand(len(entries) == 1, 'ambiguous upstream runtime file')
            demand(archive.read(entries[0]) == (root / 'runtime' / filename).read_bytes(),
                   'runtime engine changed from K224')
            compared.append(filename)
    return {'stored_cases': len(cases), 'symbolic_steps': 1431799, 'all_446_rows_in_stored_coverage': True,
            'files_byte_identical_to_vendored_K224': compared,
            'scope': 'Binding and stored-certificate integrity only; fresh universal runtime is a separate replay.'}


def audit(root):
    for relative, expected in PINS.items():
        demand(sha(root / relative) == expected, 'pinned artifact differs: ' + relative)
    parent, ps, ph = table(root / 'folds/parent226.k.tm')
    kt, ks, kh = table(root / 'folds/candidate223.k.tm')
    rt, rs, rh = table(root / 'results/candidate223.k.tm')
    nt, ns, nh = table(root / 'results/candidate223.tm')
    lt, ls, lh = table(root / 'results/candidate223.legacy.tm')
    demand((ps, ph, ks, kh, rs, rh, ns, nh, ls, lh) == (0, 254, 0, 254, 0, 254, 0, 223, 95, 254),
           'start/halt conventions differ')
    demand(kt == rt and len(kt) == 446, 'delivered K table differs')
    spec = read_json(root / 'folds/folds.json')
    certificate = read_json(root / 'folds/fold_certificate.json')
    final, folds = check_folds(parent, spec, certificate)
    demand(final == kt, 'three folds do not produce the final literal K table')
    negative = []
    for name in ('false_predecessor_tag', 'missing_inductive_support', 'wrong_reclaimed_branch'):
        altered = copy.deepcopy(spec)
        if name == 'false_predecessor_tag':
            altered['folds'][0]['invariant']['157']['-1'] = 1
        elif name == 'missing_inductive_support':
            del altered['folds'][1]['invariant']['159']
        else:
            altered['folds'][1]['a1'][2] = 173
        try:
            check_folds(parent, altered, certificate)
        except ValueError as error:
            negative.append({'test': name, 'result': 'REJECTED', 'reason': str(error)})
        else:
            raise ValueError('negative control unexpectedly accepted: ' + name)
    return {'status': 'INDEPENDENT_K223_MACHINE_AUDIT_PASS', 'pins': PINS,
            'fold_theorem': 'For every initial binary tape on the integers and every head position, '
                            'parent226 and candidate223 started in state 0 halt together. '
                            'Each old step has a positive finite exact whole-tape simulation block.',
            'folds': folds, 'negative_controls': negative,
            'literal_tables': check_maps(root, kt, nt, lt),
            'blank_bootstrap': check_bootstrap(root, nt),
            'runtime_binding': runtime_binding(root, lt),
            'limitations': 'This audit does not independently rederive the logical source calibration '
                           'or run the full universal runtime engine. Those are separately replayed. '
                           'The local fold proof is ordinary mathematical induction, not a proof-assistant endpoint.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--portable', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    answer = audit(args.portable)
    args.output.write_text(json.dumps(answer, indent=2) + '\n')
    print(json.dumps({k: answer[k] for k in ('status', 'literal_tables', 'blank_bootstrap', 'runtime_binding')}, indent=2))
