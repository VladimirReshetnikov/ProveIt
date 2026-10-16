#!/usr/bin/env python3
"""Exact-word grammar search over the full published equality-preserving AX.

Uses attributed, unchanged rebracket_axioms.py and pinned Wade backend inputs.
This is a bounded compiler experiment, not a ZFC machine correctness proof.
"""
from pathlib import Path
import argparse
from collections import Counter
import hashlib
import importlib
import json
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--archive', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--seeds', type=int, default=1000)
    args = ap.parse_args()
    if not __debug__:
        raise RuntimeError('Run without -O; supplied auditors use assertions')
    root = args.archive.resolve()
    sys.path.insert(0, str(root/'vendor/ProveIt/Computability/BusyBeaver/Research/ZFC'))
    sys.path.insert(0, str(root/'vendor/one_schema_machine'))
    import recover_wade_dag as recover
    import theory_backend_experiment as theory
    import rebracket_axioms as grammar
    nodes, names = recover.parse_dag(recover.git_bytes(None, 'ZF/m254/coq/prog/Dag254.v').decode())
    word, _, contract = theory.old_contract(nodes)
    independently_expanded = [v for q in grammar.axiom_word(nodes)
                              for v in theory.expand(nodes, q)]
    if word != independently_expanded:
        raise ValueError('Independently expanded full AX words differ')
    if not all(grammar.bounder(nodes)(f'ENode {q}') == (0, 0) for q in set(word)):
        raise ValueError('A retained macro can escape reassociation scope')
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    best, counters = None, {}
    for alpha in (1, 2, 4, 8):
        counts = Counter()
        for seed in range(args.seeds):
            residual, productions = grammar.repair(word, seed, alpha)
            newnodes, newnames, axroot = grammar.transform(nodes, names, residual, productions)
            count = len(newnodes)
            counts[count] += 1
            key = count, len(productions), len(residual), alpha, seed
            if best is None or key < best[0]:
                best = key, newnodes, newnames, axroot, residual, productions
                print(json.dumps({'best': key}), flush=True)
        counters[alpha] = dict(sorted(counts.items()))
    key, newnodes, newnames, axroot, residual, productions = best
    certificate, stats = grammar.bisimulation(nodes, newnodes)
    backend_path = root/'vendor/ProveIt/lib/jeff-busy-beaver-zfc254/ZF/generator'
    sys.path.insert(0, str(backend_path))
    backend = importlib.import_module('TMBuilder')
    machine = grammar.compile_dag(backend, newnodes, newnames)
    grammar.reextract(machine, newnodes, newnames)
    machine.save(str(out/'full_equality_preserving_named.tm'))
    states = {q for q, _ in machine.states}
    for name, data in (
        ('baseline_dag.json', {'root': 0, 'nodes': nodes, 'names': names}),
        ('candidate_dag.json', {'root': 0, 'nodes': newnodes, 'names': newnames, 'axioms_root': axroot}),
        ('rm_bisimulation.json', certificate),
        ('grammar.json', {'word': word, 'residual': residual, 'productions': productions}),
    ):
        (out/name).write_text(json.dumps(data, indent=2, sort_keys=True)+'\n')
    evidence = {
        'baseline_decision_nodes': len(nodes),
        'candidate_decision_nodes': len(newnodes),
        'full_original_equality_logic_and_theory_retained': True,
        'same_AX_macro_word': True,
        'macro_word_length': len(word),
        'closed_macros': len(set(word)),
        'symbolic_contract': contract,
        'best_recipe': {'alpha': key[3], 'seed': key[4]},
        'grammar_productions': len(productions),
        'residual_length': len(residual),
        'search_seeds_per_alpha': args.seeds,
        'histograms': counters,
        'working_states': len(states),
        'framework_states': sum(q[0].isdigit() for q in states),
        'transition_rows': len(machine.states),
        'missing_rows': [[q, b] for q in sorted(states) for b in ('0', '1') if (q, b) not in machine.states],
        'named_table_sha256': hashlib.sha256((out/'full_equality_preserving_named.tm').read_bytes()).hexdigest(),
        'rm_bisimulation': stats,
        'compiler_simulation_formally_verified': False,
        'new_ZFC_state_bound_claimed': False,
        'generator_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (out/'results.json').write_text(json.dumps(evidence, indent=2, sort_keys=True)+'\n')
    print(json.dumps(evidence, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
