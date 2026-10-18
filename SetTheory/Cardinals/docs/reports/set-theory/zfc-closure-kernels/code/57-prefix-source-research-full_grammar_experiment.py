"""Compare overlap-safe Re-Pair on two COMPLETE original AX tokenizations.

The original equality logic, CP/GIC theory, base-four constructors, and public
Wade framework are retained. The source-08 grammar/certificate tools are loaded
from their unchanged intake copies, with attribution recorded in the output.
This is a register-program compiler experiment, not a binary-TM/ZFC endpoint.
All generated artifacts and timings stay in an outside-checkout directory.
"""
from __future__ import annotations

import argparse
from collections import Counter
import copy
from functools import cache
import hashlib
import importlib
import importlib.util
import json
from pathlib import Path
import random
import sys
import time

import recover_wade_dag as recover
import theory_backend_experiment as theory

ROOT = Path(__file__).resolve().parents[4]
REPORT = ROOT / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels'


def load_file(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def expand(residual, productions):
    expanded = {}
    for i, (a, b) in enumerate(productions):
        expanded[300 + i] = expanded.get(a, [a]) + expanded.get(b, [b])
    return [token for item in residual for token in expanded.get(item, [item])]


def safe_repair(word, seed, exponent):
    """Weight actual nonoverlapping replacements; omit unusable overlap pairs."""
    rng, seq, productions = random.Random(seed), list(word), []
    diagnostics = Counter()
    while True:
        counts = Counter(zip(seq, seq[1:]))
        for pair in list(counts):
            if pair[0] != pair[1]:
                continue
            actual = position = 0
            while position + 1 < len(seq):
                if tuple(seq[position:position + 2]) == pair:
                    actual += 1
                    position += 2
                else:
                    position += 1
            if actual != counts[pair]:
                diagnostics['overlapping_pair_weights_corrected'] += 1
                if counts[pair] >= 2 and actual < 2:
                    diagnostics['unusable_raw_repeat_pairs_removed'] += 1
            counts[pair] = actual
        choices = [(pair, count) for pair, count in counts.items() if count >= 2]
        if not choices:
            if expand(seq, productions) != word:
                raise ValueError('overlap-safe grammar changed the source word')
            return seq, productions, dict(diagnostics)
        pair = rng.choices([p for p, _ in choices],
                           [n ** exponent for _, n in choices])[0]
        new, position = [], 0
        while position < len(seq):
            if position + 1 < len(seq) and tuple(seq[position:position + 2]) == pair:
                new.append(300 + len(productions))
                position += 2
            else:
                new.append(seq[position])
                position += 1
        if len(seq) - len(new) < 2:
            raise ValueError('nonoverlapping frequency contract failed')
        productions.append(pair)
        seq = new


def self_check(legacy):
    witness = [1, 1, 1, 2, 3, 2, 3]
    differing_seeds = []
    for seed in range(16):
        old_seq, old_rules = legacy(witness, seed, 4)
        new_seq, new_rules, _ = safe_repair(witness, seed, 4)
        if expand(old_seq, old_rules) != witness:
            raise ValueError('legacy grammar expansion failed')
        if len(new_seq) != 5 or len(new_rules) != 1:
            raise ValueError('overlap-safe repeat regression failed')
        if (old_seq, old_rules) != (new_seq, new_rules):
            differing_seeds.append(seed)
    if not differing_seeds:
        raise ValueError('negative overlap control no longer distinguishes algorithms')
    return dict(witness=witness, seeds=16, differing_seeds=differing_seeds)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def normalize(machine):
    working = {q for q, _ in machine.states}
    missing = [(q, b) for q in sorted(working) for b in ('0', '1')
               if (q, b) not in machine.states]
    if missing != [('1.inc', '1')]:
        raise ValueError('unexpected missing-row convention')
    ordered = [machine.start] + sorted(working - {machine.start})
    labels = {q: i for i, q in enumerate(ordered)}
    labels['halt'] = len(ordered)
    text = ['#! start 0']
    for q in ordered:
        for b in ('0', '1'):
            action = machine.states.get((q, b))
            w, d, target = ((b, 'R', 'halt') if action is None else
                            (action.write, action.direction, action.nextstate))
            text.append(f'{labels[q]} {b} {w} {d} {labels[target]}')
    return ('\n'.join(text) + '\n').encode(), labels, missing


def dispatch_depth(nodes):
    """Wade generate() charges one dispatcher state per consecutive-zero level."""
    @cache
    def zeros(q):
        first = nodes[q][0]
        return 1 + (zeros(int(first.split()[1])) if first.startswith('ENode ') else 0)
    return max(2, max(map(zeros, nodes)))


def framework_leaves(nodes):
    return {(bit, e) for es in nodes.values() for bit, e in enumerate(es)
            if not e.startswith('ENode ')}


def mutation_checks(verifier, source, candidate, certificate, out):
    original = json.loads(certificate.read_text())
    inc = next(i for i, row in enumerate(original['pairs'])
               if row['instruction'].startswith('EInc '))
    dec = next(i for i, row in enumerate(original['pairs'])
               if row['instruction'].startswith('EDecnz '))
    results = []
    for kind in ('wrong_operation', 'missing_pair', 'duplicate_pair',
                 'wrong_zero_successor', 'wrong_positive_successor', 'wrong_initial'):
        data = copy.deepcopy(original)
        if kind == 'wrong_operation':
            data['pairs'][inc]['instruction'] = 'EHalt'
        elif kind == 'missing_pair':
            data['pairs'].pop()
        elif kind == 'duplicate_pair':
            data['pairs'].append(copy.deepcopy(data['pairs'][0]))
        elif kind == 'wrong_initial':
            data['initial'] = 1
        else:
            branch = int(kind == 'wrong_positive_successor')
            data['pairs'][dec]['successors'][branch] = len(data['pairs'])
        path = out / f'mutation-{kind}.json'
        write_json(path, data)
        rejected = False
        try:
            verifier.verify(source, candidate, path)
        except (AssertionError, ValueError, IndexError, KeyError):
            rejected = True
        if not rejected:
            raise ValueError(f'bad certificate accepted: {kind}')
        results.append(dict(mutation=kind, rejected=True))
    return results


def main():
    if not __debug__:
        raise RuntimeError('Run without -O: inherited verifiers use assertions')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seeds', type=int, default=1000)
    parser.add_argument('--start-seed', type=int, default=0)
    parser.add_argument('--exponents', type=int, nargs='+', default=[1, 2, 4, 8])
    parser.add_argument('--compare-legacy', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    if out == ROOT or ROOT in out.parents:
        parser.error('output must be outside the checkout')
    if args.seeds <= 0 or args.start_seed < 0 or any(n <= 0 for n in args.exponents):
        parser.error('require positive seed count/exponents and nonnegative start')
    out.mkdir(parents=True, exist_ok=True)
    helper_path = REPORT / 'code/08-schema-machine-rebracket_axioms.py'
    verifier_path = REPORT / 'code/08-schema-machine-verify_rm_certificate.py'
    helper = load_file('source08_rebracket', helper_path)
    verifier = load_file('source08_independent_verifier', verifier_path)
    source = recover.SNAPSHOT / 'ZF/m254/coq/prog/Dag254.v'
    nodes, names = recover.parse_dag(recover.git_bytes(None, 'ZF/m254/coq/prog/Dag254.v').decode())
    expanded, _, contract = theory.old_contract(nodes)
    words = dict(coarse=list(helper.axiom_word(nodes)), expanded=expanded)
    if [m for q in words['coarse'] for m in theory.expand(nodes, q)] != expanded:
        raise ValueError('tokenizations have different fully expanded programs')
    bounds = helper.bounder(nodes)
    for word in words.values():
        if any(bounds(f'ENode {q}') != (0, 0) for q in set(word)):
            raise ValueError('source macro escapes reassociation context')
    control = self_check(helper.repair)
    for name in ('TMBuilder.py', 'tm.py', 'tmdb.py', 'LICENSE.wade'):
        (out / name).write_bytes(recover.git_bytes(None, 'ZF/generator/' + name))
    sys.path.insert(0, str(out))
    backend = importlib.import_module('TMBuilder')
    original_leaves = framework_leaves(nodes)
    best = None
    histograms, decision_histograms, changes, diagnostics = {}, {}, {}, Counter()
    framework_checks, depths = {}, {}
    def evaluate(lane, algorithm, exponent, seed, seq, grammar):
        nonlocal best
        if expand(seq, grammar) != words[lane]:
            raise ValueError('grammar changed source token word')
        nn, nm, root = helper.transform(nodes, names, seq, grammar)
        if framework_leaves(nn) != original_leaves:
            raise ValueError('register/control leaves changed')
        depth = dispatch_depth(nn)
        framework = 55 + depth
        if depth not in framework_checks:
            sample = helper.compile_dag(backend, nn, nm)
            helper.reextract(sample, nn, nm)
            states = {q for q, _ in sample.states}
            actual_framework = sum(q[0].isdigit() for q in states)
            if actual_framework != framework or len(states) != len(nn)+framework:
                raise ValueError('dispatcher cost model disagrees with actual backend')
            framework_checks[depth] = dict(decision_nodes=len(nn), framework_states=framework,
                                           total_states=len(states), every_edge_reextracted=True)
        depths[lane][depth] += 1
        cost = len(nn) + framework
        key = cost, len(nn), len(grammar), len(seq), lane, algorithm, exponent, seed
        if best is None or key < best['key']:
            best = dict(key=key, lane=lane, algorithm=algorithm, exponent=exponent, seed=seed,
                        nodes=nn, names=nm, root=root, word=words[lane], residual=seq,
                        productions=grammar, dispatcher_depth=depth, framework=framework)
            print(json.dumps(dict(new_minimum_states=cost, decision_nodes=len(nn),
                                  framework_states=framework, lane=lane, algorithm=algorithm,
                                  exponent=exponent, seed=seed)), flush=True)
        return len(nn), cost
    start = time.monotonic()
    for lane, word in words.items():
        histograms[lane] = {}; decision_histograms[lane] = {}; depths[lane] = Counter()
        changes[lane] = dict(different_grammars=0, different_node_counts=0,
                             different_state_counts=0,
                             safe_smaller=0, legacy_smaller=0)
        for exponent in args.exponents:
            histogram = Counter()
            legacy_histogram = Counter()
            decision_histogram, legacy_decision_histogram = Counter(), Counter()
            for seed in range(args.start_seed, args.start_seed + args.seeds):
                seq, grammar, diag = safe_repair(word, seed, exponent)
                diagnostics.update(diag)
                count, cost = evaluate(lane, 'safe', exponent, seed, seq, grammar)
                histogram[cost] += 1; decision_histogram[count] += 1
                if args.compare_legacy:
                    old_seq, old_grammar = helper.repair(word, seed, exponent)
                    old_count, old_cost = evaluate(lane, 'legacy', exponent, seed, old_seq, old_grammar)
                    legacy_histogram[old_cost] += 1; legacy_decision_histogram[old_count] += 1
                    changes[lane]['different_grammars'] += (seq, grammar) != (old_seq, old_grammar)
                    changes[lane]['different_node_counts'] += count != old_count
                    changes[lane]['different_state_counts'] += cost != old_cost
                    changes[lane]['safe_smaller'] += cost < old_cost
                    changes[lane]['legacy_smaller'] += cost > old_cost
            histograms[lane][exponent] = dict(safe=dict(sorted(histogram.items())),
                                             legacy=dict(sorted(legacy_histogram.items())))
            decision_histograms[lane][exponent] = dict(safe=dict(sorted(decision_histogram.items())),
                                                       legacy=dict(sorted(legacy_decision_histogram.items())))
            print(json.dumps(dict(lane=lane, exponent=exponent, best_states=best['key'][0],
                                  elapsed_seconds=time.monotonic()-start)), flush=True)
    machine = helper.compile_dag(backend, best['nodes'], best['names'])
    helper.reextract(machine, best['nodes'], best['names'])
    machine.save(str(out / 'candidate.named.tm'))
    table, labels, missing = normalize(machine)
    (out / 'candidate.tm').write_bytes(table)
    write_json(out / 'labels.json', labels)
    certificate, stats = helper.bisimulation(nodes, best['nodes'])
    write_json(out / 'baseline_dag.json', dict(root=0, nodes=nodes, names=names))
    candidate = out / 'candidate_dag.json'
    write_json(candidate, dict(root=0, nodes=best['nodes'], names=best['names'],
                              axioms_root=best['root']))
    write_json(out / 'grammar.json', {k: best[k] for k in ('word', 'residual', 'productions')})
    cert_path = out / 'rm_bisimulation.json'
    write_json(cert_path, certificate)
    checked = verifier.verify(source, candidate, cert_path)
    mutations = mutation_checks(verifier, source, candidate, cert_path, out)
    states = {q for q, _ in machine.states}
    framework = sum(q[0].isdigit() for q in states)
    if framework != best['framework'] or len(states) != best['key'][0]:
        raise ValueError('measured backend differs from charged dispatcher cost')
    result = dict(source_upstream_commit=recover.COMMIT,
                  driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  source08_helper=str(helper_path.relative_to(ROOT)),
                  source08_verifier=str(verifier_path.relative_to(ROOT)),
                  full_original_equality_logic_and_theory_retained=True,
                  original_symbolic_contract=contract,
                  token_lengths={k: len(v) for k, v in words.items()},
                  samples_per_lane=len(args.exponents) * args.seeds,
                  exponents=args.exponents, seed_start=args.start_seed,
                  compare_legacy=args.compare_legacy, histograms=histograms,
                  histogram_unit='total working states including variable dispatcher',
                  decision_histograms=decision_histograms,
                  dispatch_depth_histograms=depths,
                  framework_cost_model='55 fixed states plus max_zeros dispatcher depth; unchanged register/control leaves checked',
                  actual_compiler_framework_checks=framework_checks,
                  paired_comparisons=changes, overlap_diagnostics=dict(diagnostics),
                  overlap_self_check=control,
                  winner={k: best[k] for k in ('lane', 'algorithm', 'exponent', 'seed', 'key')},
                  decision_nodes=len(best['nodes']), working_states=len(states),
                  framework_states=framework, named_rows=len(machine.states),
                  winner_dispatcher_depth=best['dispatcher_depth'],
                  total_rows=2 * len(states), missing_rows=missing,
                  total_table_sha256=hashlib.sha256(table).hexdigest(),
                  named_table_sha256=hashlib.sha256((out/'candidate.named.tm').read_bytes()).hexdigest(),
                  rm_bisimulation=stats, independent_rm_check=checked,
                  mutations=mutations, improves_prior269=len(states) < 269,
                  binary_compiler_or_ZFC_endpoint_proved=False,
                  elapsed_seconds=time.monotonic() - start)
    write_json(out / 'results.json', result)
    print(json.dumps({k: result[k] for k in ('winner', 'decision_nodes', 'working_states',
                                          'improves_prior269', 'paired_comparisons',
                                          'overlap_diagnostics', 'elapsed_seconds')}, indent=2))


if __name__ == '__main__':
    main()
