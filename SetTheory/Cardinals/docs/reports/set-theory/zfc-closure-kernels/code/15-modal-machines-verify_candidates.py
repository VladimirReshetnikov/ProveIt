#!/usr/bin/env python3
"""Rebuild both frozen AX-grammar candidates from hash-pinned upstream sources.

Use --repo /path/to/ProveIt, or first run fetch_dependencies.py. This verifier
checks executable certificates; it does not prove a compiler simulation or
the consistency calibration. Dependencies are never modified or redistributed.
"""
from __future__ import annotations
import argparse
import functools
import hashlib
import importlib
import json
from pathlib import Path
import sys
import tempfile

if not __debug__:
    raise SystemExit('Run without -O: this verifier requires Python assertions.')

HERE = Path(__file__).resolve().parent


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_tree(value, allowed):
    if isinstance(value, int) and not isinstance(value, bool) and value in allowed:
        return value
    if isinstance(value, list) and len(value) == 2:
        return tuple(read_tree(x, allowed) for x in value)
    raise ValueError('Grammar node must be one allowed macro or an ordered pair')


def word(tree):
    if isinstance(tree, int): return (tree,)
    return word(tree[0]) + word(tree[1])


def effects(builder):
    normal = ('normal', 0)
    @functools.lru_cache(None)
    def visit(node):
        if not isinstance(node, int):
            if node == 'halt': return frozenset({('halt', 0)})
            for prefix, kind in (('_break.', 'break'), ('_continue.', 'continue')):
                if node.startswith(prefix):
                    level = int(node[len(prefix):])
                    assert level >= 1
                    return frozenset({(kind, level)})
            if node.endswith('.inc'): return frozenset({normal})
            if node.endswith('.decnz'): return frozenset({normal, ('break', 1)})
            raise ValueError('Unknown primitive: ' + node)
        left, right = builder.sequences[node].seq
        exits = set()
        for kind, level in visit(left):
            if kind == 'break':
                exits.add(normal if level == 1 else ('break', level - 1))
            elif kind != 'normal':
                exits.add((kind, level))
            else:
                for kind, level in visit(right):
                    if kind != 'continue': exits.add((kind, level))
                    elif level > 1: exits.add(('continue', level - 1))
                    # continue1 on the right repeats the current node. It
                    # creates no new kind of finite exit; divergence is allowed.
        return frozenset(exits)
    return visit


def numeric_table(named):
    """Independent totalization and canonical numbering of the named source."""
    rows, start = {}, None
    for raw in named.decode().splitlines():
        line = raw.strip()
        if not line: continue
        if line.startswith('#!'):
            directive = line.split()
            assert directive[:2] == ['#!', 'start'] and len(directive) == 3
            assert start is None
            start = directive[2]
            continue
        if line.startswith('#'): continue
        q, read, write, move, target = line.split()
        assert read in ('0', '1') and write in ('0', '1') and move in ('L', 'R')
        key = q, int(read)
        assert key not in rows
        rows[key] = int(write), move, target
    states = {q for q, _ in rows}
    assert start in states
    assert {target for _, _, target in rows.values()} - states == {'halt'}
    missing = [(q, b) for q in sorted(states) for b in (0, 1) if (q, b) not in rows]
    assert missing == [('1.inc', 1)]
    rows['1.inc', 1] = 1, 'R', 'halt'
    names = [start] + sorted(states - {start})
    labels = {q: i for i, q in enumerate(names)}
    labels['halt'] = len(names)
    numeric = {}
    lines = ['#! start 0']
    for q in names:
        for b in (0, 1):
            w, move, target = rows[q, b]
            numeric[labels[q], b] = w, move, labels[target]
            lines.append(f'{labels[q]} {b} {w} {move} {labels[target]}')
    return ('\n'.join(lines) + '\n').encode(), numeric, len(names)


def table_facts(rows, count):
    assert set(rows) == {(q, b) for q in range(count) for b in (0, 1)}
    reached, todo = {0}, [0]
    while todo:
        q = todo.pop()
        if q == count: continue
        for b in (0, 1):
            target = rows[q, b][2]
            assert 0 <= target <= count
            if target not in reached:
                reached.add(target); todo.append(target)
    classes = {q: int(q == count) for q in range(count + 1)}
    rounds = 0
    while True:
        lookup, fresh = {}, {}
        for q in range(count + 1):
            signature = ('halt',) if q == count else tuple(
                (rows[q, b][0], rows[q, b][1], classes[rows[q, b][2]]) for b in (0, 1))
            fresh[q] = lookup.setdefault(signature, len(lookup))
        rounds += 1
        stable = len(set(fresh.values())) == len(set(classes.values()))
        classes = fresh
        if stable: break
    return {'graph_reachable_working_states': len(reached - {count}),
            'bisimulation_working_classes': len(set(classes.values())) - 1,
            'bisimulation_refinement_rounds': rounds,
            'halt_edges': sum(t == count for _, _, t in rows.values())}


def verify_one(record, theory, recover, backend, scratch):
    nodes, names = recover.parse_dag(recover.git_bytes(None, 'ZF/m254/coq/prog/Dag254.v').decode())
    _, logical, _ = theory.old_contract(nodes)
    baseline = theory.build_variant(backend, nodes, names, logical, record['source_variant'])
    baseline.generate(); baseline.tm.gc()
    baseline_file = scratch / ('baseline-' + record['name'] + '.tm')
    baseline.tm.save(str(baseline_file))
    assert sha(baseline_file.read_bytes()) == record['baseline_named_sha256']
    assert len({q for q, _ in baseline.tm.states}) == record['baseline_working_states']
    expected = tuple(theory.equality_free_rows(reordered=True, dual=record['dual_rho6']))
    tree = read_tree(record['tree'], theory.MACROS)
    assert word(tree) == expected == tuple(record['macro_word'])
    assert len(expected) == 138

    builder = recover.builder_from_dag(backend, nodes, names)
    builder.sequence_lookup = {s.seq: i for i, s in enumerate(builder.sequences)}
    @functools.lru_cache(None)
    def reify(t):
        if isinstance(t, int): return t
        return builder.add_sequence((reify(t[0]), reify(t[1])))
    newroot = reify(tree)
    builder.sequences[newroot].name = 'AX_fixed_word().0'
    for q, sequence in enumerate(builder.sequences):
        if q != 1:
            sequence.seq = tuple(newroot if x == 1 else x for x in sequence.seq)
    assert builder.sequences[118].seq[0] == 156
    builder.sequences[118].seq = (157, builder.sequences[118].seq[1])
    def expanded_program(source_builder, node, stop=None):
        if node == stop: return '<AX>'
        if not isinstance(node, int): return node
        left, right = source_builder.sequences[node].seq
        return (expanded_program(source_builder, left, stop),
                expanded_program(source_builder, right, stop))
    assert all(expanded_program(baseline, q) == expanded_program(builder, q)
               for q in theory.MACROS)
    source_ax = baseline.sequences[149].seq[0]
    assert expanded_program(baseline, 0, source_ax) == expanded_program(builder, 0, newroot)
    effect = effects(builder)
    assert all(effect(q) == frozenset({('normal', 0)}) for q in theory.MACROS)
    reachable = tuple(builder.reachable())
    @functools.lru_cache(None)
    def zero_run(q):
        return 1 + zero_run(builder.sequences[q].seq[0]) if isinstance(q, int) else 0
    max_zeros = max(zero_run(q) for q in reachable)
    assert max_zeros == record['maximum_decoder_zero_run']
    assert len(reachable) == record['decision_states']
    builder.name_sequences(); builder.generate(); builder.tm.gc()
    named_file = scratch / (record['name'] + '.tm')
    builder.tm.save(str(named_file))
    named = named_file.read_bytes()
    assert sha(named) == record['named_sha256']
    generated, rows, count = numeric_table(named)
    assert count == record['working_states']
    assert sha(generated) == record['numeric_sha256']
    assert generated == (HERE / record['numeric_filename']).read_bytes()
    states = {q for q, _ in builder.tm.states}
    assert sum(q[0].isdigit() for q in states) == record['framework_states']
    facts = table_facts(rows, count)
    return {'name': record['name'], 'baseline_working_states': record['baseline_working_states'],
            'working_states': count, 'complete_binary_rows': len(rows),
            'decision_states': len(reachable), 'framework_states': record['framework_states'],
            'maximum_decoder_zero_run': max_zeros, 'macro_calls': len(expected),
            'exact_macro_word_verified': True, 'all_19_macro_bodies_unchanged': True,
            'program_context_outside_AX_unchanged': True, 'all_19_macro_effects_normal': True,
            'numeric_sha256': sha(generated), **facts,
            'compiler_simulation_proved': False, 'ZFC_consistency_calibration_proved': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=HERE / 'upstream')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    manifest = json.loads((HERE / 'source_pins.json').read_text())
    repo = args.repo.resolve()
    for path, digest in manifest['files'].items():
        file = repo / path
        if not file.is_file():
            raise SystemExit(f'Missing {file}; run fetch_dependencies.py or supply --repo.')
        if sha(file.read_bytes()) != digest:
            raise SystemExit('Source pin mismatch: ' + path)
    source = repo / 'Computability/BusyBeaver/Research/ZFC'
    sys.path.insert(0, str(source))
    import theory_backend_experiment as theory
    import recover_wade_dag as recover
    with tempfile.TemporaryDirectory(prefix='zfc-grammar-') as directory:
        scratch = Path(directory)
        for name in ('TMBuilder.py', 'tm.py', 'tmdb.py', 'LICENSE.wade'):
            (scratch / name).write_bytes(recover.git_bytes(None, 'ZF/generator/' + name))
        sys.path.insert(0, str(scratch))
        backend = importlib.import_module('TMBuilder')
        records = [json.loads((HERE / name).read_text()) for name in
                   ('grammar-250-oldrho6.json', 'grammar-249-dual.json')]
        evidence = {'pinned_repo_commit': manifest['commit'],
                    'verified_source_files': len(manifest['files']),
                    'candidates': [verify_one(r, theory, recover, backend, scratch) for r in records]}
    encoded = json.dumps(evidence, indent=2) + '\n'
    if args.output: args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__': main()
