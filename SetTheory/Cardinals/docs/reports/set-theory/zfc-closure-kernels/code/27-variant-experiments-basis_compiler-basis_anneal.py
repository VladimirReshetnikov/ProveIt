#!/usr/bin/env python3
"""Directed extension of basis_search.py; every uncached cost is compiled."""
import argparse
import copy
import json
import math
from pathlib import Path
import random
import time
import basis_search as s


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--iterations', type=int, default=20000)
    ap.add_argument('--rng-seed', type=int, default=10617)
    ap.add_argument('--vary-bundle', action='store_true')
    ap.add_argument('--input', type=Path, default=s.HERE / 'results/comparison.json')
    ap.add_argument('--output', type=Path, default=s.HERE / 'anneal_results')
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    init = json.loads(args.input.read_text())
    nodes, names, rows, bundle, perms, bases, specsha = s.setup()
    rng = random.Random(args.rng_seed)
    records, bests, evaluations = [], {}, {}
    start = time.monotonic()
    for basis in ('KSP', 'KBP'):
        best = copy.deepcopy(init['bests'][basis])
        if args.vary_bundle:
            for k, v in {'C': 2, 'G': 1, 'outer_order': 16, 'tree': 1}.items():
                best['recipe'].setdefault(k, v)
        current = copy.deepcopy(best)
        cache = {}
        for it in range(1, args.iterations + 1):
            if it % 2000 == 0:
                current = copy.deepcopy(best)
            recipe = copy.deepcopy(current['recipe'])
            k = rng.randrange(13 if args.vary_bundle else 9)
            if k == 0:
                recipe['prop_perms'][rng.randrange(3)] = rng.randrange(6)
            elif k == 1:
                a, b = rng.sample(range(3), 2)
                recipe['prop_order'][a], recipe['prop_order'][b] = recipe['prop_order'][b], recipe['prop_order'][a]
            elif k in (2, 3):
                recipe['other_perms'][rng.randrange(7)] = rng.randrange(6)
            elif k == 4:
                a, b = rng.sample(range(7), 2)
                recipe['other_order'][a], recipe['other_order'][b] = recipe['other_order'][b], recipe['other_order'][a]
            elif k in (5, 6, 7):
                recipe['seed'] = rng.randrange(4096)
            elif k == 8:
                recipe['alpha'] = rng.choice((1, 2, 4, 8))
            elif k == 9:
                recipe['C'] = rng.randrange(8)
            elif k == 10:
                recipe['G'] = rng.randrange(4)
            elif k == 11:
                recipe['outer_order'] = rng.randrange(24)
            else:
                recipe['tree'] = rng.randrange(5)
            word, _, _ = s.program(rows, bundle, perms, bases, basis, recipe)
            key = tuple(word), recipe['seed'], recipe['alpha']
            if key not in cache:
                cache[key] = s.compile_word(nodes, names, word, recipe)[0]
            cost = cache[key]
            candidate = {'basis': basis, 'iteration': it, 'recipe': recipe, 'cost': cost}
            temperature = .3 + 1.0 * (1 - (it % 2000) / 2000)
            diff = current['cost']['working_states'] - cost['working_states']
            if diff >= 0 or rng.random() < math.exp(diff / temperature):
                current = candidate
            if cost['working_states'] < best['cost']['working_states']:
                best = copy.deepcopy(candidate)
                records.append(best)
                print(json.dumps(best), flush=True)
                s.write_json(args.output / f'{basis}_best_recipe.json', best)
            if it % 10000 == 0:
                print(json.dumps({'basis': basis, 'iteration': it, 'best': best['cost'],
                                  'actual_compilations': len(cache), 'elapsed': time.monotonic() - start}), flush=True)
        bests[basis] = best
        evaluations[basis] = len(cache)
        s.save_winner(args.output, basis, best, nodes, names, rows, bundle, perms, bases)
    result = {'bests': bests, 'iterations_per_basis': args.iterations,
              'actual_compilations': evaluations, 'improvements': records,
              'rng_seed': args.rng_seed, 'source19_baseline': init['source19_baseline'],
              'vary_bundle': args.vary_bundle,
              'parent_comparison_sha256': s.sha(args.input.read_bytes()),
              'elapsed_seconds': time.monotonic() - start,
              'all_uncached_costs_from_actual_compilation': True,
              'overall_record_claimed': False}
    s.write_json(args.output / 'comparison.json', result)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
