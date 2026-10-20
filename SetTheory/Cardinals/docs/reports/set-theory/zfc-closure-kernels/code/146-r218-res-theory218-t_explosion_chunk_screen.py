#!/usr/bin/env python3
"""Finite chunk-preserving follow-up to the uncalibrated T+EXP screen."""
import itertools
import json
from pathlib import Path
import sys

import t_explosion_source_screen as t
from grammar_search import nodes

a, z, s = t.a, t.z, t.s
OUT = Path(__file__).parent / 't_explosion_chunks'


def main():
    OUT.mkdir(exist_ok=True)
    evaluate, model = t.hardware.model(t.TABLE, t.OLD, t.ENGINE)
    old_chunks = a.chunks(t.OLD, 895, 1178)
    assert len(old_chunks) == 3
    pushes = [z.MACRO[k] for k in (166, 121, 168)]
    records, best, best_tree = [], 10**9, None
    for binder, matrix in itertools.permutations(range(3), 2):
        tt = [pushes[binder], pushes[matrix], z.MACRO[180],
              pushes[matrix], z.MACRO[119]]
        for em in range(3):
            ee = [z.MACRO[177], pushes[em], z.MACRO[119]]
            for reverse in (False, True):
                atoms = ee + tt if reverse else tt + ee
                for cut1, cut2 in itertools.combinations(range(1, 8), 2):
                    pieces = [z.seq(atoms[:cut1]), z.seq(atoms[cut1:cut2]),
                              z.seq(atoms[cut2:])]
                    new = t.OLD
                    for (lo, hi, old_piece), piece in reversed(list(zip(old_chunks, pieces))):
                        new = a.splice(new, lo, hi, piece)
                    assert z.flat(new) == z.flat(t.OLD)[:895] + tuple(x for atom in atoms for x in z.flat(atom)) + z.flat(t.OLD)[1178:]
                    live = nodes(new)
                    fixed = set().union(*(model['node_states'].get(n, ()) for n in live))
                    fresh = [n for n in live if not s.leaf(n) and n not in model['node_states']]
                    bare = model['nondecoder'] + len(fixed) + len(fresh)
                    record = dict(binder=binder, matrix=matrix, explosion_matrix=em,
                                  explosion_first=reverse, cuts=[cut1, cut2],
                                  metrics=s.metrics(new), bare_cost=bare)
                    if bare <= best:
                        record.update(evaluate(new))
                        if record['cost_lower_bound'] < best:
                            best = record['cost_lower_bound']
                            best_tree = new
                            print('BEST', json.dumps(record), flush=True)
                            path = OUT / f'best{best}.sites.json'
                            path.write_bytes(s.compact(s.sites(new)))
                            record['source'] = str(path.relative_to(t.ROOT))
                    else:
                        record['screened_out_by_bare_lower_bound'] = True
                    records.append(record)
    sites = s.sites(best_tree)
    assert s.graph_arithmetic(sites)[0] == s.graph_intervals(sites)
    result = dict(status='UNCALIBRATED_SOURCE_SCREEN_ONLY', layouts=len(records),
                  minimum_hardware_lower_bound=best,
                  minimum_DAG=min(x['metrics']['dag_nodes'] for x in records),
                  full_objective_evaluations=sum('cost_lower_bound' in x for x in records),
                  note='Bare-cost pruning cannot discard a strict improvement in this preserved-row objective.',
                  records=records)
    (OUT / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print('DONE', json.dumps({k: v for k, v in result.items() if k != 'records'}), flush=True)


if __name__ == '__main__':
    main()
