#!/usr/bin/env python3
"""Finite screen of the other one-Q, three-implication T+EXP fusions."""
import itertools
import json
from pathlib import Path

import t_explosion_source_screen as t
from grammar_search import nodes

a, z, s = t.a, t.z, t.s
OUT = Path(__file__).parent / 'fused_d_equivalents'
FORMULAS = (((('P', 'A'), 'F'), 'A'), ((('F', 'A'), 'P'), 'A'))


def truth(formula, values):
    return values[formula] if isinstance(formula, str) else (not truth(formula[0], values)) or truth(formula[1], values)


def main():
    OUT.mkdir(exist_ok=True)
    evaluate, model = t.hardware.model(t.TABLE, t.OLD, t.ENGINE)
    chunks = a.chunks(t.OLD, 895, 1178)
    pushes = [z.MACRO[k] for k in (166, 121, 168)]
    records, best = [], 10**9
    original = ((('P', 'F'), 'F'), 'A')
    for variant, formula in enumerate(FORMULAS):
        assert all(truth(formula, dict(zip('PAF', bits))) == truth(original, dict(zip('PAF', bits)))
                   for bits in itertools.product((False, True), repeat=3))
        for binder, matrix in itertools.permutations(range(3), 2):
            def atoms(f):
                if f == 'P':
                    return [pushes[binder], pushes[matrix], z.MACRO[180]]
                if f == 'A':
                    return [pushes[matrix]]
                if f == 'F':
                    return [z.MACRO[177]]
                if f[1] == 'F':
                    return atoms(f[0]) + [z.MACRO[218]]
                return atoms(f[0]) + atoms(f[1]) + [z.MACRO[119]]
            word = atoms(formula)
            assert sum(len(z.flat(atom)) for atom in word) == 234
            layouts = [('whole', last) for last in (False, True)]
            layouts += [('chunks', cuts) for cuts in itertools.combinations(range(1, len(word)), 2)]
            for kind, layout in layouts:
                if kind == 'whole':
                    new = a.splice(t.OLD, 895, 1178, z.seq(word), layout)
                else:
                    c1, c2 = layout
                    pieces = [z.seq(word[:c1]), z.seq(word[c1:c2]), z.seq(word[c2:])]
                    new = t.OLD
                    for (lo, hi, old_piece), piece in reversed(list(zip(chunks, pieces))):
                        new = a.splice(new, lo, hi, piece)
                live = nodes(new)
                fixed = set().union(*(model['node_states'].get(n, ()) for n in live))
                fresh = [n for n in live if not s.leaf(n) and n not in model['node_states']]
                bare = model['nondecoder'] + len(fixed) + len(fresh)
                record = dict(variant=variant, binder=binder, matrix=matrix,
                              layout=kind, detail=layout, metrics=s.metrics(new), bare_cost=bare)
                if bare <= best:
                    record.update(evaluate(new))
                    if record['cost_lower_bound'] < best:
                        best = record['cost_lower_bound']
                        sites = s.sites(new)
                        assert s.graph_arithmetic(sites)[0] == s.graph_intervals(sites)
                        destination = OUT / f'best{best}.sites.json'
                        destination.write_bytes(s.compact(sites))
                        record['source'] = str(destination.relative_to(t.ROOT))
                        print('BEST', json.dumps(record), flush=True)
                else:
                    record['screened_out_by_bare_lower_bound'] = True
                records.append(record)
    result = dict(status='UNCALIBRATED_SOURCE_SCREEN_ONLY', formulas=FORMULAS,
                  layouts=len(records), replacement_leaves=234,
                  minimum_hardware_lower_bound=best,
                  minimum_DAG=min(x['metrics']['dag_nodes'] for x in records),
                  full_objective_evaluations=sum('cost_lower_bound' in x for x in records),
                  calibration='Equivalent to T+EXP; its consistency calibration is OPEN.',
                  records=records)
    (OUT / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print('DONE', json.dumps({k: v for k, v in result.items() if k != 'records'}), flush=True)


if __name__ == '__main__':
    main()
