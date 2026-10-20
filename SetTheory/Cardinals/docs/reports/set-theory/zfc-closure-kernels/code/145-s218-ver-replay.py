#!/usr/bin/env python3
"""Offline replay of the two new 219-state machines in this research packet.

The source/calculus proofs are ordinary mathematics, documented in the report.
The runtime checker uses induction over arbitrary unary lengths and finite
spare lists. It is not a proof-assistant kernel. --quick omits that runtime
replay; it still checks hashes, construction, source, decoder, and blank start.
"""
from pathlib import Path
from collections import deque
import argparse
import hashlib
import json
import sys
import time
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
ARCHIVE_HASH = '04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'
PARENT_HASHES = {
    'K220': '132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00',
    'K221': 'a06c99b775193d9642a2734b7dd5fe7b72736fbdf9d9d8be438321d5e5d57ba4',
}
DEPENDENCIES = {
    'portable/build221.py': '3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
    'portable/source_language.py': '4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
    'portable/runtime/vendor/symbolic_runtime.py': 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
    'portable/runtime/vendor/independent_runtime.py': '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
    'portable/runtime/reference_results/legacy_mapping.json': '26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf',
}
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
SEED = [3, 0, 0, 0, 3, 0, 0, 0, 0]


def need(test, reason):
    if not test:
        raise ValueError(reason)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def extract(archive, destination, expected):
    need(sha(archive) == expected, 'Archive hash mismatch: ' + str(archive))
    destination.mkdir(parents=True, exist_ok=True)
    root = destination.resolve()
    with zipfile.ZipFile(archive) as z:
        for name in z.namelist():
            target = (root / name).resolve()
            need(target == root or root in target.parents, 'Unsafe ZIP member')
        z.extractall(root)


def parents(output):
    inputs = output / 'inputs'
    extract(ROOT / 'vendor/K219_Construction_2026-10-20.zip', inputs, ARCHIVE_HASH)
    k219 = inputs / 'K219_Construction_2026-10-20'
    extract(k219 / 'portable/vendor/K220_Construction_2026-10-20.zip', inputs,
            PARENT_HASHES['K220'])
    k220 = inputs / 'K220_Construction_2026-10-20'
    extract(k220 / 'portable/vendor/K221_Construction_2026-10-20.zip', inputs,
            PARENT_HASHES['K221'])
    k221 = inputs / 'K221_Construction_2026-10-20'
    for name, expected in DEPENDENCIES.items():
        need(sha(k221 / name) == expected, 'Dependency hash mismatch: ' + name)
    return k219, k221


def source_rho6(source, old, new):
    need(len(old) == len(new) == 4744, 'rho6 source length')
    expected = {(966, 'CD'), (971, 'CI'), (1144, 'CD'), (1149, 'CI')}
    changed = set()
    for i, (a, b) in enumerate(zip(old, new)):
        need(a[0] == b[0], 'rho6 source path changed')
        if a != b:
            need(a[1:] == [a[1], 3] and b[1:] == [a[1], 5], 'Unexpected operand change')
            changed.add((i, a[1]))
    need(changed == expected, 'rho6 source patch differs')
    # The new word is the already-used, closed parameter-b push macro.
    oldword = [row[1:] for row in old]
    newword = [row[1:] for row in new]
    for lo in (947, 1125):
        need(oldword[lo:lo + 26] == oldword[947:973], 'Original c-push mismatch')
        need(newword[lo:lo + 26] == oldword[66:92], 'Replacement is not the existing b-push')
    for rows in (old, new):
        need(source.graph_arithmetic(rows)[0] == source.graph_intervals(rows),
             'Independent source resolvers disagree')
    need([row[1] for row in source.graph_arithmetic(old)[0]] ==
         [row[1] for row in source.graph_arithmetic(new)[0]],
         'rho6 control-flow topology changed')
    return {
        'status': 'EXACT_RHO6_PUSH_REPLACEMENT_PASS',
        'changed_primitive_ordinals': [966, 971, 1144, 1149],
        'closed_push_intervals': [[947, 973], [1125, 1151]],
        'replacement_reference_interval': [66, 92],
        'ordinary_calculus_argument': 'D(a,c) becomes D(a,b); both ranges are all D(i,A).',
        'proof_translations': {'old_to_new_AX': '(a,b,c) -> (a,c,0)',
                               'new_to_old_AX': '(a,b,c) -> (a,0,b)'},
        'scope': 'Exact source syntax and control graph; macro contracts and axiom-range proof in report.'
    }


def source_nop(source, old, new, output):
    graphs = []
    for rows in (old, new):
        g = source.graph_intervals(rows)
        need(source.graph_arithmetic(rows)[0] == g, 'Independent source resolvers disagree')
        graphs.append(g)
    oldg, graph = graphs
    cut, end = 4597, 4603
    need([len(old), len(new)] == [4744, 4750], 'NOP source sizes')
    need([x[1:] for x in old] == [x[1:] for x in new[:cut] + new[end:]],
         'NOP changes the old primitive word')
    need([x[1:] for x in new[cut:end]] == [
        ['CD', 7], ['CI', 6], ['CC', 2], ['CD', 4], ['CI', 5], ['CC', 2]],
        'NOP insertion differs')
    # Bit 1 denotes zero; bit 2 denotes a positive natural value.
    facts = [None] * len(new)
    facts[0] = tuple(1 if x == 0 else 2 for x in SEED)
    queue = deque([0])

    def posts(i, values):
        op, a = new[i][1:]
        successors = graph[i][1]
        if op == 'CH':
            return []
        if op == 'CI':
            v = list(values); v[a] = 2
            return [(successors[0], tuple(v))]
        if op == 'CD':
            result = []
            if values[a] & 1:
                v = list(values); v[a] = 1
                result.append((successors[0], tuple(v)))
            if values[a] & 2:
                v = list(values); v[a] = 3
                result.append((successors[1], tuple(v)))
            return result
        return [(successors[0], values)]

    work = 0
    while queue:
        i = queue.popleft(); work += 1
        for j, values in posts(i, facts[i]):
            merged = values if facts[j] is None else tuple(a | b for a, b in zip(values, facts[j]))
            if facts[j] != merged:
                facts[j] = merged; queue.append(j)
    # Independently recheck post-fixpoint closure of the computed certificate.
    for i, values in enumerate(facts):
        if values is not None:
            for j, post in posts(i, values):
                need(facts[j] is not None and all((a | b) == b for a, b in zip(post, facts[j])),
                     'Abstract certificate is not inductive')
    need(facts[cut][4] == facts[cut][7] == facts[4600][4] == facts[4600][7] == 1,
         'Required NOP input is not forced zero')
    need(all(facts[i] is None for i in (4598, 4599, 4601, 4602)),
         'NOP body not proved unreachable')

    def contract(i):
        visited = set()
        while cut <= i < end:
            need(i not in visited and i in (cut, cut + 3), 'Unexpected NOP control entry')
            visited.add(i)
            need(facts[i][new[i][2]] == 1, 'Unproved zero guard')
            i = graph[i][1][0]
        return i if i < cut else i - 6

    edges = 0
    for i, (effect, successors) in enumerate(oldg):
        j = i if i < cut else i + 6
        neffect, nsuccessors = graph[j]
        need(effect == neffect and successors == list(map(contract, nsuccessors)),
             'NOP contraction changes guarded source behavior')
        edges += len(successors)
    (output / 'zero_facts.json').write_text(json.dumps(facts, separators=(',', ':')) + '\n')
    return {'status': 'INDUCTIVE_ZERO_AND_NOP_STUTTERING_PASS', 'inserted_interval': [cut, end],
            'admitted_inserted_path': [4597, 4600], 'required_zero_registers': [4, 7],
            'abstract_work_items': work, 'checked_outside_guarded_edges': edges,
            'scope': 'Finite inductive invariant and exact contraction, from the stated seed.'}


def boot(table):
    # One sparse simulation and an independent fixed-array simulation.
    state, head, ones = 0, 0, set()
    steps = 312617
    for tick in range(steps):
        need(state != 254, 'Blank startup halted early')
        w, d, state = table[state, int(head in ones)]
        if w: ones.add(head)
        else: ones.discard(head)
        head += d
    width, origin = 200000, 100000
    cells = bytearray(width); q, h = 0, origin
    for count in range(steps):
        need(q != 254, 'Dense startup halted early')
        w, d, q = table[q, cells[h]]; cells[h] = w; h += d
        need(0 <= h < width, 'Dense simulation escaped its represented window')
    dense = {i - origin for i, bit in enumerate(cells) if bit}
    need((q, h - origin, dense) == (state, head, ones), 'Independent startup simulations disagree')
    expected = {head - 1, 139}
    physical = [0] * 9
    for i, j in enumerate(PHY): physical[j] = SEED[i]
    cursor = 140
    for value in physical + [1] * 130:
        cursor += 1
        expected.update(range(cursor, cursor + value + 1)); cursor += value + 1
    need((steps, state, head) == (312617, 84, -5) and ones == expected,
         'Unexpected complete blank-start configuration')
    return {'status': 'DUAL_COMPLETE_BLANK_STARTUP_PASS', 'steps': steps,
            'dispatcher': state, 'head': head, 'header': 139, 'extra_gap': 80,
            'logical_seed': SEED, 'spare_values': [1] * 130,
            'complete_one_cells': sorted(ones), 'all_other_cells': 0}


def runtime_check(table, sites, parent, output, runtime):
    mapping = {int(q): int(z) for q, z in json.loads(
        (parent / 'portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
    for q in {q for q, bit in table} | {254}:
        if q not in mapping: mapping[q] = q + 1000
    need(len(set(mapping.values())) == len(mapping), 'Runtime label map is not injective')
    need(mapping[84] == 96 and mapping[254] == 254, 'Runtime entry labels differ')
    legacy = {(mapping[q], bit): (w, d, mapping[z]) for (q, bit), (w, d, z) in table.items()}
    lemmas, blocks = runtime.prove_blocks(legacy)
    cases = []; used = set(); started = time.monotonic()
    for i, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            answer = runtime.case(legacy, lemmas, site, positive)
            used.update(answer.pop('rows')); answer.pop('trace')
            cases.append({'index': i, 'positive': positive, **answer})
            if len(cases) % 1000 == 0:
                print(output.name, 'PROVED', len(cases), flush=True)
    expected = sum(2 if x[1] == 'CD' else 1 for x in sites)
    need(len(cases) == expected, 'Runtime proof census incomplete')
    dump(output / 'runtime_cases.json', cases)
    return {'status': 'ALL_PRIMITIVE_INTERFACES_PROVED', 'cases': len(cases),
            'expected_cases': expected, 'symbolic_steps': sum(c['symbolic_steps'] for c in cases),
            'minimum_duration_constant': min(c['duration'][0] for c in cases),
            'seconds': time.monotonic() - started, 'block_schemas': blocks,
            'scope': 'All independent natural registers and decrement guards; arbitrary extra gap, '
                     'first spare value, and finite remaining spare list; whole tape, positive duration.',
            'bounds': '4000 bounds proof search only, not machine time or represented values.',
            'proof_status': 'Executable ordinary mathematics; not a proof-assistant kernel certificate.'}


def main():
    need(__debug__ and not sys.flags.optimize, 'Do not use Python -O or PYTHONOPTIMIZE')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', type=Path, required=True)
    ap.add_argument('--variant', choices=['nop219', 'rho6_219', 'all'], default='all')
    ap.add_argument('--quick', action='store_true')
    args = ap.parse_args(); out = args.output_dir.resolve()
    need(not out.exists(), 'Use a new output directory')
    out.mkdir(parents=True)
    baseline, parent = parents(out)
    sys.path.insert(0, str(parent / 'portable'))
    import build221 as builder
    import source_language as source
    sys.path.insert(0, str(parent / 'portable/runtime/vendor'))
    import symbolic_runtime as runtime
    original = builder.read_table((baseline / 'machine/k219.native.tm').read_bytes())
    oldsites = json.loads((baseline / 'machine/sites219.json').read_text())
    manifest = json.loads((ROOT / 'machines/manifest.json').read_text())
    selected = list(manifest) if args.variant == 'all' else [args.variant]
    receipts = {}
    for name in selected:
        spec = manifest[name]; directory = ROOT / 'machines' / name
        for filename, expected in spec['sha256'].items():
            need(sha(directory / filename) == expected, 'Machine file hash mismatch: ' + filename)
        table = builder.read_table((directory / 'native.tm').read_bytes())
        need(len(table) == 438 and len({q for q, bit in table}) == 219, 'Working-state count differs')
        reconstructed = original.copy()
        for change in spec['patch']:
            key = change['state'], change['read']
            need(list(reconstructed[key]) == change['old'], 'Patch precondition differs')
            reconstructed[key] = tuple(change['new'])
        need(reconstructed == table, 'Construction patch does not reconstruct the table')
        rows = json.loads((directory / 'sites.json').read_text()); tree = source.tree(rows)
        need(source.sites(tree) == rows and source.metrics(tree) == spec['source_metrics'],
             'Source metrics or order differ')
        builder.decoder_map(table, tree)
        # Check the complete relabelled table without assuming canonical halt254.
        state_map = {int(q): int(z) for q, z in json.loads((directory / 'state_map.json').read_text()).items()}
        need(len(state_map) == 220 and len(set(state_map.values())) == 220, 'Canonical map differs')
        need(state_map[0] == 0 and state_map[254] == 219, 'Canonical endpoints differ')
        canonical = {(state_map[q], bit): (w, d, state_map[z]) for (q, bit), (w, d, z) in table.items()}
        need(builder.table_bytes(canonical) == (directory / 'canonical.tm').read_bytes(),
             'Canonical table is not the declared bijective relabelling')
        result_dir = out / name; result_dir.mkdir()
        source_receipt = (source_nop(source, oldsites, rows, result_dir) if name == 'nop219'
                          else source_rho6(source, oldsites, rows))
        startup = boot(table)
        dump(result_dir / 'source.json', source_receipt)
        dump(result_dir / 'startup.json', startup)
        result = {'working_states': 219, 'rows': 438, 'hashes': spec['sha256'],
                  'source': source_receipt['status'], 'startup': startup['status'],
                  'runtime': 'NOT_REPLAYED_QUICK_MODE'}
        if not args.quick:
            runtime_receipt = runtime_check(table, rows, parent, result_dir, runtime)
            dump(result_dir / 'runtime.json', runtime_receipt)
            result['runtime'] = runtime_receipt['status']
        receipts[name] = result
        print(name, json.dumps(result), flush=True)
    dump(out / 'replay.json', {'status': 'QUICK_REPLAY_PASS' if args.quick else 'FULL_VARIANT_REPLAY_PASS',
         'variants': receipts, 'parent_archive_sha256': ARCHIVE_HASH,
         'dependencies': DEPENDENCIES, 'driver_sha256': sha(Path(__file__)),
         'scope': 'Transport from the pinned K219 parent; ordinary source/calculus proofs are in the report.'})


if __name__ == '__main__':
    main()
