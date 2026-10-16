#!/usr/bin/env python3
"""Actually compile complete three-parameter replacements for rho8.

This is an engineering experiment.  The RM certificate relates a selected
modified-basis source program to its rebracketing, NOT to the original program.
The public Wade backend is used without modifications.  Every reported cost
comes from its generated, garbage-collected transition table, including boot
and all dispatcher depths.  Neither Python checker nor compiler is a Coq proof.
"""
from __future__ import annotations
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import importlib
import itertools
import json
from pathlib import Path
import random
import sys
import time
import types

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
# Keep the vendored source byte-exact, but specialize its repository-relative
# path before execution.  This also works when the archive is unpacked shallowly
# (where the original Path(__file__).parents[4] would not exist).
r = types.ModuleType('recover_wade_dag')
r.__file__ = str(HERE / 'recover_wade_dag.py')
sys.modules[r.__name__] = r
_recovery_text = (HERE / 'recover_wade_dag.py').read_text()
assert _recovery_text.count('ROOT = Path(__file__).resolve().parents[4]') == 1
_recovery_text = _recovery_text.replace('ROOT = Path(__file__).resolve().parents[4]',
                                      'ROOT = Path(__file__).resolve().parent')
exec(compile(_recovery_text, r.__file__, 'exec'), r.__dict__)
r.ROOT = HERE
r.SNAPSHOT = HERE / 'snapshot'
import theory_backend_experiment as t
import rebracket_axioms as g
from verify_rm_certificate import Machine
sys.path.insert(0, str(HERE / 'backend'))
backend = importlib.import_module('TMBuilder')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def rename(f, perm):
    if isinstance(f, tuple):
        return f[0], rename(f[1], perm), rename(f[2], perm)
    return perm.get(f, f)


def and_parts(f):
    if isinstance(f, tuple) and f[0] == 'imp' and f[2] == 1:
        a = f[1]
        if isinstance(a, tuple) and a[0] == 'imp':
            b = a[2]
            if isinstance(b, tuple) and b[0] == 'imp' and b[2] == 1:
                return a[1], b[1]
    return None


def variants(f):
    parts = and_parts(f)
    if parts:
        return [out for a, b in itertools.product(variants(parts[0]), variants(parts[1]))
                for out in (t.And(a, b), t.And(b, a))]
    if isinstance(f, tuple):
        return [(f[0], a, b) for a, b in itertools.product(variants(f[1]), variants(f[2]))]
    return [f]


def trees(items):
    if len(items) == 1:
        return items
    return [t.And(a, b) for cut in range(1, len(items))
            for a, b in itertools.product(trees(items[:cut]), trees(items[cut:]))]


def coarsen(word):
    # Existing node161 is exactly the closed macro push-a; implication.
    out, i = [], 0
    while i < len(word):
        if word[i:i + 2] == [166, 119]:
            out.append(161)
            i += 2
        else:
            out.append(word[i])
            i += 1
    return out


@lru_cache(None)
def bundle_components():
    spec, _ = t.published_spec()
    return (variants(spec['bundle_C']('a', 'b', 'c')),
            variants(spec['bundle_G']('a', 'b', 'c')),
            [t.Imp(rel('a', 'b'), t.All('c', rel('a', 'b'))) for rel in (t.Rel, t.Eq)])


@lru_cache(None)
def choose_bundle(ci, gi, oi, ti):
    C, G, V = bundle_components()
    components = [C[ci], G[gi], *V]
    order = list(itertools.permutations(range(4)))[oi]
    return trees([components[i] for i in order])[ti]


def setup():
    raw = (HERE / 'snapshot/Dag254.v').read_bytes()
    assert sha(raw) == g.SOURCE_SHA256
    nodes, names = r.parse_dag(raw.decode())
    t.old_contract(nodes)
    spec, specsha = t.published_spec()
    rows = spec['ax_rows']('a', 'h', 'b', 'c', 'u')
    bundle = choose_bundle(2, 1, 16, 1)
    perms = [dict(zip(('a', 'b', 'c'), p)) for p in itertools.permutations(('a', 'b', 'c'))]
    I = t.Imp
    K = I('a', I('b', 'a'))
    S = I(I('a', I('b', 'c')), I(I('a', 'b'), I('a', 'c')))
    B = I(I('a', 'b'), I(I('b', 'c'), I('a', 'c')))
    P = I(I(I('a', 'b'), 'a'), 'a')
    return nodes, names, rows, bundle, perms, {'KSP': [K, S, P], 'KBP': [K, B, P]}, specsha


def program(rows, bundle, perms, bases, basis, recipe):
    if 'C' in recipe:
        bundle = choose_bundle(recipe['C'], recipe['G'], recipe['outer_order'], recipe['tree'])
    if basis == 'L':
        fs = rows[1:]
    else:
        prop = [rename(f, perms[pi]) for f, pi in zip(bases[basis], recipe['prop_perms'], strict=True)]
        prop = [prop[i] for i in recipe['prop_order']]
        other = [rename(rows[i], perms[pi]) for i, pi in zip(range(2, 9), recipe['other_perms'], strict=True)]
        other = [other[i] for i in recipe['other_order']]
        # GEN reads old h first.  read_b happens once.  No fourth stream read.
        fs = prop + other
    word = [166, 121, 180, 176] + [m for f in fs for m in t.emit(f)] + t.emit(bundle) + t.TAIL
    actual, events = t.symbolic(word)
    assert actual == ['old_top', t.All('a', 'h'), *fs, bundle]
    if basis != 'L':
        assert 158 not in word and 208 not in word
        assert word.count(176) == 1
    return word, fs, events


def compile_word(nodes, names, word, recipe):
    seq, grammar = g.repair(coarsen(word), recipe['seed'], recipe['alpha'])
    nn, nm, ax = g.transform(nodes, names, seq, grammar)
    machine = g.compile_dag(backend, nn, nm)
    working = {q for q, _ in machine.states}
    framework = {q for q in working if q[0].isdigit()}
    decisions = working - framework
    assert len(decisions) == len(nn)
    result = {'working_states': len(working), 'framework_states': len(framework),
              'decision_states': len(decisions), 'macro_count': len(word),
              'grammar_productions': len(grammar), 'residual_length': len(seq)}
    return result, nn, nm, ax, machine


def verify_certificate(ref, candidate, cert):
    # Reuse the separately implemented string/integer path machine, not the
    # generator's tuple path arithmetic or any backend implementation.
    old, new = Machine(ref), Machine(candidate)
    records = cert['pairs']
    assert cert['initial'] == 0 and cert['branch_order'] == 'EDecnz: zero, positive'
    assert old.contract('') == (records[0]['old'], records[0]['instruction'])
    assert new.contract('') == (records[0]['new'], records[0]['instruction'])
    seen = set()
    for record in records:
        a, b, label = record['old'], record['new'], record['instruction']
        assert (a, b) not in seen
        seen.add((a, b))
        assert old.lookup(a) == (a, label) and new.lookup(b) == (b, label)
        lt, rt = old.targets(a, label), new.targets(b, label)
        assert len(lt) == len(rt) == len(record['successors'])
        for index, l, rr in zip(record['successors'], lt, rt, strict=True):
            assert type(index) is int and 0 <= index < len(records)
            target = records[index]
            assert l == (target['old'], target['instruction'])
            assert rr == (target['new'], target['instruction'])
    reached, pending = set(), [0]
    while pending:
        j = pending.pop()
        if j not in reached:
            reached.add(j)
            pending.extend(records[j]['successors'])
    assert len(reached) == len(records)
    return {'verified': True, 'related_pairs': len(records), 'reference_nodes': len(ref),
            'candidate_nodes': len(candidate), 'formalized': False,
            'binary_compiler_proved': False,
            'scope': 'modified-basis program versus its exact RM rebracketing'}


def save_winner(out, basis, best, nodes, names, rows, bundle, perms, bases):
    d = out / basis
    d.mkdir(exist_ok=True)
    word, fs, events = program(rows, bundle, perms, bases, basis, best['recipe'])
    bundle = t.symbolic(word)[0][-1]
    cost, nn, nm, ax, machine = compile_word(nodes, names, word, best['recipe'])
    assert cost == best['cost']
    g.reextract(machine, nn, nm)
    assert g.bounder(nn)('ENode 0') == (0, 0)
    machine.save(str(d / 'candidate.named.tm'))
    working = {q for q, _ in machine.states}
    labels = [machine.start] + sorted(working - {machine.start})
    ids = {q: i for i, q in enumerate(labels)}
    halt = len(labels)
    table = ['#! start 0']
    missing = []
    for q in labels:
        for bit in ('0', '1'):
            a = machine.states.get((q, bit))
            if a is None:
                missing.append([ids[q], int(bit)])
                write, direction, target = bit, 'R', halt
            else:
                assert a.nextstate in ids or a.nextstate == 'halt'
                write, direction, target = a.write, a.direction, ids.get(a.nextstate, halt)
            table.append(f'{ids[q]} {bit} {write} {direction} {target}')
    (d / 'candidate.tm').write_text('\n'.join(table) + '\n')
    write_json(d / 'state_names.json', {'names': labels, 'halt': halt})
    write_json(d / 'candidate.dag.json', {'root': 0, 'axioms_root': ax, 'nodes': nn, 'names': nm})
    # Direct source: no Re-Pair rules at all, fully right-associated emission.
    # Its expanded macro word is the same, but its decoder is much larger.
    ref, rn, ra = g.transform(nodes, names, coarsen(word), [])
    cert, stats = g.bisimulation(ref, nn)
    checked = verify_certificate(ref, nn, cert)
    write_json(d / 'reference.dag.json', {'root': 0, 'axioms_root': ra, 'nodes': ref, 'names': rn})
    write_json(d / 'rm_certificate.json', cert)
    evidence = {'basis': basis, 'recipe': best['recipe'], 'cost': cost,
                'logical_rows_ast': fs, 'theory_bundle_ast': bundle,
                'macro_word': word, 'events': events,
                'basis_is_complete': True, 'fourth_stream_parameter_removed': basis != 'L',
                'equality_logic_and_base4_codec_retained': True,
                'bundle_recipe': {k: best['recipe'].get(k, v)
                                  for k, v in {'C': 2, 'G': 1, 'outer_order': 16, 'tree': 1}.items()},
                'all_decision_edges_reextracted': True, 'rm_bisimulation': stats,
                'independent_rm_certificate_check': checked,
                'numeric_sha256': sha((d / 'candidate.tm').read_bytes()),
                'totalized_missing_rows': missing, 'transitions': 2 * halt,
                'blank_tape_initializer_included': True, 'start_state': 0,
                'blank_symbol': 0, 'uncounted_halt_state': halt,
                'new_consistency_bound_proved': False,
                'formalized_binary_compiler': False,
                'interpretation_warning': 'Finite RM certificate proves only modified source to compressed source; neither original proof-stream equivalence nor ZFC endpoint is asserted.'}
    write_json(d / 'evidence.json', evidence)
    return evidence


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=HERE / 'results')
    ap.add_argument('--seeds', type=int, default=1000)
    ap.add_argument('--permutation-trials', type=int, default=3000)
    ap.add_argument('--rng-seed', type=int, default=10616)
    args = ap.parse_args()
    assert __debug__, 'run without -O'
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    nodes, names, rows, bundle, perms, bases, specsha = setup()
    initial = {'prop_perms': [0, 0, 0], 'prop_order': [0, 1, 2],
               'other_perms': [0] * 7, 'other_order': list(range(7)), 'seed': 341, 'alpha': 4}
    baseline_word, _, _ = program(rows, bundle, perms, bases, 'L', initial)
    baseline_cost, *_ = compile_word(nodes, names, baseline_word, initial)
    print(json.dumps({'baseline': 'source19_L', 'cost': baseline_cost}), flush=True)
    start = time.monotonic()
    bests, counts, records, sample_costs = {}, Counter(), [], {}
    rng = random.Random(args.rng_seed)
    for basis in ('KSP', 'KBP'):
        best = None
        costs = Counter()
        for trial in range(args.seeds + args.permutation_trials):
            recipe = dict(initial)
            if trial < args.seeds:
                recipe['seed'] = trial
            else:
                # Compare schema parameter permutations and formula sharing
                # while retaining all complete logical rows and original set theory.
                recipe['seed'] = rng.randrange(max(args.seeds, 2048))
                recipe['alpha'] = rng.choice((1, 2, 4, 8))
                recipe['prop_perms'] = [rng.randrange(6) for _ in range(3)]
                recipe['prop_order'] = rng.sample(range(3), 3)
                if trial % 2:
                    recipe['other_perms'] = [rng.randrange(6) for _ in range(7)]
                if trial % 3 == 0:
                    recipe['other_order'] = rng.sample(range(7), 7)
            word, _, _ = program(rows, bundle, perms, bases, basis, recipe)
            cost, *_ = compile_word(nodes, names, word, recipe)
            counts[basis] += 1
            costs[cost['working_states']] += 1
            if best is None or cost['working_states'] < best['cost']['working_states']:
                best = {'basis': basis, 'trial': trial, 'recipe': recipe, 'cost': cost}
                records.append(best)
                print(json.dumps(best), flush=True)
            if trial == args.seeds - 1:
                write_json(out / f'{basis}_initial_seed_search.json',
                           {'trials': args.seeds, 'fixed_recipe_except_seed': initial,
                            'seed_range': [0, args.seeds - 1], 'best': best,
                            'actual_compiled_cost_histogram': dict(costs)})
        bests[basis] = best
        sample_costs[basis] = dict(costs)
        print(json.dumps({'basis_done': basis, 'trials': counts[basis],
                          'best': best['cost'], 'elapsed': time.monotonic() - start}), flush=True)
    evidence = {basis: save_winner(out, basis, bests[basis], nodes, names, rows, bundle, perms, bases)
                for basis in bests}
    result = {'source19_baseline': baseline_cost, 'bests': bests, 'trials': dict(counts),
              'improvements': records, 'actual_compiled_cost_histograms': sample_costs,
              'elapsed_seconds': time.monotonic() - start, 'rng_seed': args.rng_seed,
              'pinned_Dag254_sha256': g.SOURCE_SHA256, 'spec_sha256': specsha,
              'backend_sha256': {fn: sha((HERE / 'backend' / fn).read_bytes())
                                 for fn in ('TMBuilder.py', 'tm.py', 'tmdb.py')},
              'generated_binary_tables': {basis: data['numeric_sha256'] for basis, data in evidence.items()},
              'all_costs_from_actual_compilation': True, 'overall_record_claimed': False}
    write_json(out / 'comparison.json', result)
    print(json.dumps({'final_comparison': {b: bests[b]['cost'] for b in bests},
                      'output': str(out), 'elapsed': result['elapsed_seconds']}), flush=True)


if __name__ == '__main__':
    main()
