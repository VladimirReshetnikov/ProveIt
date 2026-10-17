"""Reproduce the odometer controls against a read-only pinned ProveIt checkout.

The original full DAG and every runtime row are retained. Only the counted
blank initializer changes. Requires no network and modifies no repository.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True

from odometer_initializer import make_auxiliary, make_register_clock, make_zero_single_sentinel, simulate
from exact_state_quotient import minimize, verify, parse, encode

PROVEIT_PIN = '61e77836565f63582561f54745f633d50efd9c7d'


def attach(mb, original, init, contract):
    reverse = {q: name for name, q in original.labels.items()}
    runtime = {(reverse[q], b): (w, d, reverse[t])
               for (q, b), (w, d, t) in original.table.items()
               if not reverse[q].startswith('i:')}
    runtime_rows = len(runtime)
    assert all(not t.startswith('i:') for w, d, t in runtime.values())
    named = runtime | init
    live = {q for q, b in named}
    assert len(named) == 2*len(live)
    assert all(t in live or t == 'halt' for w, d, t in named.values())
    start = contract['start']
    order = [start] + sorted(live-{start})
    labels = {q: i for i, q in enumerate(order)} | {'halt': len(order)}
    table = {(labels[q], b): (w, d, labels[t]) for (q, b), (w, d, t) in named.items()}
    # Exact full-row preservation is stronger than finite runtime sampling.
    reverse_new = {i: q for q, i in labels.items()}
    for (q, b), (w, d, t) in runtime.items():
        w2, d2, t2 = table[labels[q], b]
        assert (w2, d2, reverse_new[t2]) == (w, d, t)
    roles = Counter(q.split(':')[0] for q in live)
    evidence = dict(proveit_pin=PROVEIT_PIN,
                    upstream_pin=mb.COMMIT,
                    inherited_input_DAG_sha256=original.evidence['input_DAG_sha256'],
                    initializer=contract,
                    working_states=len(live), binary_rows=len(table),
                    runtime_rows_preserved_exactly=runtime_rows,
                    states_by_prefix=dict(sorted(roles.items())),
                    kernel_checked=False, new_consistency_bound_claimed=False)
    machine = mb.MiraMachine(table, labels, original.sites, evidence, contract['gap'],
                             tuple(contract['initial_registers']))
    return machine


def json_dag(path):
    obj = json.loads(path.read_text())
    root = obj['root']
    remap = {root: 0} | {q: j+1 for j, q in enumerate(
        sorted(int(k) for k in obj['nodes'] if int(k) != root))}

    def edge(value):
        if isinstance(value, str):
            return 'ENode '+str(remap[int(value.split()[1])]) if value.startswith('ENode ') else value
        kind = dict(N='ENode', I='EInc', D='EDecnz', B='EBreak', C='EContinue', H='EHalt')[value[0]]
        return kind if kind == 'EHalt' else f'{kind} {remap[value[1]] if kind == "ENode" else value[1]}'
    nodes = {remap[int(q)]: tuple(edge(e) for e in row) for q, row in obj['nodes'].items()}
    return nodes, {q: f'source_node_{q}' for q in nodes}


def check_numeric_boot(machine, contract, expected):
    q, h, tape = 0, 0, set()
    for steps in range(contract['blank_steps']+1):
        if q == machine.root:
            break
        w, d, q = machine.table[q, int(h in tape)]
        if w:
            tape.add(h)
        else:
            tape.discard(h)
        h += 1 if d == 'R' else -1
    assert q == machine.root and steps == expected['steps']
    assert h == expected['head'] and tape == set(expected['final_ones'])
    return dict(passed=True, steps=steps, head=h, one_cells=len(tape),
                whole_tape_sha256=expected['whole_tape_sha256'])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--proveit', '--repo', dest='proveit', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--one-sentinel-only', action='store_true')
    args = parser.parse_args()
    repo = args.proveit.resolve()
    out = args.output.resolve()
    if repo == out or repo in out.parents:
        raise ValueError('output must be outside the source checkout')
    head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', 'HEAD'], text=True).strip()
    if head != PROVEIT_PIN:
        raise ValueError('use the exact pinned checkout')
    source_dir = repo/'Computability/BusyBeaver/Research/ZFC'
    sys.dont_write_bytecode = True
    checked_paths = [
        'Computability/BusyBeaver/Research/ZFC/'+name
        for name in ('mira_backend.py', 'recover_wade_dag.py', 'compact_initializer.py')
    ]
    checked_paths += [
        'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/'+name
        for name in ('08-schema-machine-results-rebracketed_dag.json',
                     '19-subst-engineering-artifacts-full_logic_best.dag.json',
                     '20-complete-vendor-decoder255-data-candidate202.json')
    ]
    for path in checked_paths:
        pinned = subprocess.check_output(['git', '-C', str(repo), 'show', PROVEIT_PIN+':'+path])
        if (repo/path).read_bytes() != pinned:
            raise ValueError('required source has uncommitted changes: '+path)
    sys.path.insert(0, str(source_dir))
    import mira_backend as mb
    from recover_wade_dag import git_bytes, parse_dag
    source = git_bytes(None, mb.DAG_PATH)
    original_dag = parse_dag(source.decode())
    host = repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data'
    dag_paths = {
        'rebracket207': host/'08-schema-machine-results-rebracketed_dag.json',
        'rebracket206': host/'19-subst-engineering-artifacts-full_logic_best.dag.json',
        'decoder202': host/'20-complete-vendor-decoder255-data-candidate202.json',
    }
    dags = {'original219': original_dag} | {k: json_dag(p) for k, p in dag_paths.items()}
    out.mkdir(parents=True, exist_ok=True)
    results = []
    configurations = [
        ('original219', 'aux-np0', make_auxiliary((0,)*9, 7, 'd:0')),
        ('original219', 'aux-np2', make_auxiliary((2,)+(0,)*8, 7, 'd:0')),
    ]
    configurations += [(dag, f'register-clock-np{np}', make_register_clock(9, 'd:0', np))
                       for dag in dags for np in (0, 2)]
    if args.one_sentinel_only:
        configurations = [(dag, 'one-sentinel-np0', make_zero_single_sentinel(9, 'd:0'))
                          for dag in dags]
    for dag_name, init_name, (init, contract) in configurations:
        nodes, names = dags[dag_name]
        stem = dag_name+'-'+init_name
        original = mb.compile_dag(nodes, names, initial_registers=contract['initial_registers'],
                                   initializer='compact')
        machine = attach(mb, original, init, contract)
        machine.evidence['initializer_literal_replay'] = simulate(init, contract)
        machine.evidence['numeric_blank_boot'] = check_numeric_boot(
            machine, contract, machine.evidence['initializer_literal_replay'])
        machine.check_sites()
        path = out/(stem+'.tm')
        machine.save(path)
        reconstructed = {}
        for line in path.read_text().splitlines():
            if line.startswith('#'):
                continue
            q, b, w, d, t = line.split()
            key = int(q), int(b)
            assert key not in reconstructed
            reconstructed[key] = int(w), d, int(t)
        assert reconstructed == machine.table
        machine.evidence['table_sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
        machine.evidence['table_roundtrip_exact'] = True
        machine.evidence['table_file'] = path.name
        quotient, cert = minimize(machine.table)
        qp = out/(stem+'-quotient.tm')
        qp.write_bytes(encode(quotient))
        verify(parse(path.read_bytes()), parse(qp.read_bytes()), cert)
        cp = out/(stem+'-quotient.json')
        cp.write_text(json.dumps(cert, indent=2)+'\n')
        inverse = {q: name for name, q in machine.labels.items()}
        machine.evidence['exact_quotient'] = dict(
            states=len(quotient)//2, certificate=cp.name, table=qp.name,
            source_state_count=machine.halt,
            merged_labels=[[inverse[q] for q in group] for group in cert['nontrivial_classes']],
            table_sha256=hashlib.sha256(qp.read_bytes()).hexdigest(),
            independent_row_equations_pass=True,
            full_boot_transfers_by_exact_step_homomorphism=True)
        if dag_name in dag_paths:
            path_source = dag_paths[dag_name]
            machine.evidence['input_DAG_path'] = str(path_source.relative_to(repo))
            machine.evidence['input_DAG_file_sha256'] = hashlib.sha256(path_source.read_bytes()).hexdigest()
        (out/(stem+'-labels.json')).write_text(json.dumps(machine.labels, indent=2)+'\n')
        results.append(machine.evidence)
        print(stem, machine.halt, '->', len(quotient)//2,
              machine.evidence['symbolic_site_checks']['cases_passed'], flush=True)
    (out/'integration_results.json').write_text(json.dumps(results, indent=2)+'\n')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('assertions must be enabled')
    main()
