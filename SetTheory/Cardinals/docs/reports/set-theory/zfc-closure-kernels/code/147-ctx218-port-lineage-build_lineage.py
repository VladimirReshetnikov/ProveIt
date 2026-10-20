#!/usr/bin/env python3
"""Reconstruct K218 from pinned upstream K219, using only Python's standard library.

The explicit source grammars are construction data, not an undocumented search
history. Two independently implemented complete CFG resolvers establish source
bisimulation. Exact table reconstruction and source-prefix contracts do not
replace the separate fresh unbounded runtime and whole blank-startup proofs.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

import source_equivalence as se

HERE = Path(__file__).resolve().parent
PINS = {
    'upstream_table': 'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26',
    'upstream_source': '0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789',
    'normalized_table': '57ef76ac8b5f169db328f6ba1de8afdbb5ebb106c6187fb2333757a5a301e047',
    'final_table': '4dd4ca3893a80b99a1df52e4a57f0357eeb697255f86f43b859a1a97ef511651',
    'final_native': '3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1',
    'final_source': '1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe',
}


def require(test, message):
    if not test:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def compact(value):
    return (json.dumps(value, separators=(',', ':')) + '\n').encode('ascii')


def encode(table):
    return ('#! start 0\n' + ''.join(f'{q} {b} {w} {d} {z}\n'
            for (q, b), (w, d, z) in sorted(table.items()))).encode('ascii')


def read_table(raw):
    result, headers = {}, []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            headers.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            require((q, b) not in result and b in (0, 1) and w in (0, 1)
                    and d in ('L', 'R') and q >= 0 and z >= 0, 'Invalid table row')
            result[q, b] = [w, d, z]
    require(headers == [0], 'Expected unique start state0')
    census(result)
    require(encode(result) == raw, 'Noncanonical table bytes')
    return result


def census(table):
    states = {q for q, _ in table}
    require(0 in states and 84 in states and 254 not in states, 'Start/dispatcher/halt labels')
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Binary totality')
    require({z for w, d, z in table.values()} - states == {254}, 'No dangling target other than halt254')
    return len(states)


def expand(grammar):
    nodes = grammar['nodes']
    require(type(nodes) is list and nodes, 'Nonempty source grammar')
    built = []
    for i, node in enumerate(nodes):
        require(type(node) is list and len(node) == 2, 'Binary DAG record')
        if type(node[0]) is str:
            built.append(tuple(node))
        else:
            require(all(type(c) is int and 0 <= c < i for c in node), 'Topological DAG order')
            built.append((built[node[0]], built[node[1]]))
    root = grammar['root']
    require(type(root) is int and 0 <= root < len(nodes), 'DAG root')
    reached, todo = set(), [root]
    while todo:
        i = todo.pop()
        if i in reached:
            continue
        reached.add(i)
        if type(nodes[i][0]) is int:
            todo.extend(nodes[i])
    require(reached == set(range(len(nodes))), 'No orphan source DAG records')
    require(len(set(built)) == len(nodes), 'Minimal source grammar')
    rows = se.sites(built[root])
    require(se.tree(rows) == built[root], 'Exact full source round trip')
    require(sha(compact(rows)) == grammar['source_sha256'], 'Reconstructed source hash')
    return rows


def prefix_binding(table, rows):
    """Literal prefix proofs: arbitrary exterior is never read or modified."""
    paths = {p[:i] for p, _, _ in rows for i in range(len(p))}
    entries, traces = {}, []
    for p in sorted(paths):
        tape = {i: int(b) for i, b in enumerate(p)}
        original = tape.copy()
        q, h, steps = 84, 0, []
        while h != len(p):
            require(len(steps) < 2000, 'Prefix construction bound exceeded')
            require(h in tape and (q, tape[h]) in table, 'Prefix reads unknown exterior or halt')
            b = tape[h]
            w, d, z = table[q, b]
            steps.append([q, h, b, w, d, z])
            tape[h], q = w, z
            h += 1 if d == 'R' else -1
        require(tape == original and (q, 0) in table, 'Prefix must preserve tape and reach working state')
        entries[p] = q
        traces.append([p, q, steps])
    require(len(entries) == len(rows) - 1, 'All source interior occurrences covered')
    return dict(prefixes=len(entries), physical_source_states=len(set(entries.values())),
                literal_steps=sum(len(x[2]) for x in traces),
                entry_sha256=sha(compact(entries)), trace_sha256=sha(compact(traces)),
                unknown_exterior_reads=0), entries


def main():
    require(sys.flags.optimize == 0,
            'Run without -O, -OO or PYTHONOPTIMIZE: the downstream byte constructor uses assertions.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=HERE / 'lineage_rebuilt')
    parser.add_argument('--upstream-table', type=Path, default=HERE / 'upstream_basis/upstream219.native.tm')
    parser.add_argument('--upstream-source', type=Path, default=HERE / 'upstream_basis/upstream219.sites.json')
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    raw = args.upstream_table.read_bytes()
    source_raw = args.upstream_source.read_bytes()
    require(sha(raw) == PINS['upstream_table'], 'Pinned upstream table hash')
    require(sha(source_raw) == PINS['upstream_source'], 'Pinned upstream source hash')
    original = json.loads(source_raw)
    require(compact(original) == source_raw, 'Canonical source bytes')
    native = read_table(raw)
    recipe_raw = (HERE / 'lineage_recipe.json').read_bytes()
    recipe = json.loads(recipe_raw)
    renaming = {int(k): v for k, v in recipe['normalization'].items()}
    require(renaming == {301: 102, 302: 120}, 'Normalization identity')
    rename = lambda q: renaming.get(q, q)
    table = {(rename(q), b): [w, d, rename(z)] for (q, b), (w, d, z) in native.items()}
    require(len(table) == len(native) and sha(encode(table)) == PINS['normalized_table'], 'Bijective normalization')
    inverse = {v: k for k, v in renaming.items()}
    inv = lambda q: inverse.get(q, q)
    require(encode({(inv(q), b): [w, d, inv(z)] for (q, b), (w, d, z) in table.items()}) == raw,
            'Normalization exact byte round trip')
    reference, _ = se.graph_arithmetic(original)
    require(reference == se.graph_intervals(original), 'Baseline independent CFG resolvers')
    stages = []

    def record(name, current, rows):
        tree = se.tree(rows)
        graph, checks = se.graph_arithmetic(rows)
        require(graph == se.graph_intervals(rows) == reference, 'Complete guarded CFG equality at ' + name)
        require([r[1:] for r in rows] == [r[1:] for r in original], 'Primitive word equality at ' + name)
        require(rows[:37] == original[:37], 'First37 bootstrap source addresses at ' + name)
        metrics = se.metrics(tree)
        binding, entries = prefix_binding(current, rows)
        (out / (name + '.tm')).write_bytes(encode(current))
        (out / (name + '.sites.json')).write_bytes(compact(rows))
        (out / (name + '.binding.json')).write_bytes(compact(entries))
        stages.append(dict(stage=name, states=census(current), transition_rows=len(current),
            table_sha256=sha(encode(current)), source_sha256=sha(compact(rows)),
            source_metrics=metrics, guarded_edges=sum(len(x[1]) for x in graph),
            source_target_checks=checks, complete_guarded_CFG_equal=True,
            primitive_word_equal=True, first37_addresses_equal=True, prefix_binding=binding))

    rows = original
    record('normalized_upstream', table, rows)
    for stage in recipe['allocation_stages']:
        name = stage['name']
        if name in recipe['source_grammars']:
            rows = expand(recipe['source_grammars'][name])
        for q, b, old, new in stage['edits']:
            require(table.get((q, b)) == old, 'Old row precondition at ' + name)
            if new is None:
                del table[q, b]
            else:
                table[q, b] = new
        require(sha(encode(table)) == stage['table_sha256'], 'Stage table hash at ' + name)
        require(sha(compact(rows)) == stage['source_sha256'], 'Stage source hash at ' + name)
        require(census(table) == stage['states'], 'Stage state count')
        record(name, table, rows)
    # The downstream constructor is independently explicit. Check that its seed
    # equals the upstream reconstruction before invoking it; it is not an axiom.
    require(encode(table) == (HERE / 'basis/direct188.tm').read_bytes(), 'Downstream seed table reconstructed')
    require(compact(rows) == (HERE / 'basis/direct188.sites.json').read_bytes(), 'Downstream seed source reconstructed')
    downstream = out / 'downstream'
    result = subprocess.run([sys.executable, str(HERE / 'build218.py'), str(downstream)],
                            check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    (out / 'downstream.log').write_text(result.stdout + result.stderr)
    for name in ('reuse12', 'reuse150', 'candidate'):
        record(name, read_table((downstream / (name + '.tm')).read_bytes()),
               json.loads((downstream / (name + '.sites.json')).read_bytes()))
    require(stages[-1]['states'] == 218 and stages[-1]['transition_rows'] == 436, 'Final218 census')
    require(stages[-1]['table_sha256'] == PINS['final_table'] and
            stages[-1]['source_sha256'] == PINS['final_source'], 'Final normalized pins')
    final_native = (downstream / 'candidate.native.tm').read_bytes()
    require(sha(final_native) == PINS['final_native'] and census(read_table(final_native)) == 218, 'Final native pins')
    (out / 'candidate.native.tm').write_bytes(final_native)
    receipt = dict(status='PINNED_UPSTREAM219_TO_K218_EXACT_LINEAGE_AND_SOURCE_BISIMULATION_PASS',
        upstream_commit=recipe['upstream_commit'], pinned_inputs=PINS,
        constructor_sha256=sha(Path(__file__).read_bytes()), recipe_sha256=sha(recipe_raw),
        source_checker_sha256=sha((HERE / 'source_equivalence.py').read_bytes()),
        downstream_constructor_sha256=sha((HERE / 'build218.py').read_bytes()),
        complete_guarded_CFG_sha256=sha(compact(reference)), stages=stages,
        native_sha256=sha(final_native),
        scope='Deterministic byte reconstruction, complete all-natural source bisimulation, binary state census, and exact source-prefix contracts. Whole blank startup, unbounded primitive runtime and foundational equiconsistency are separately audited.')
    (out / 'lineage.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
