#!/usr/bin/env python3
"""Source-only census for D = N N Q_i A -> A, equivalent to T + EXP.

Its calibration against Con(ZFC) is OPEN.  The hardware objective is an
exploratory preserved-row bound, not a compiled literal-machine certificate.
"""
import itertools
import json
from pathlib import Path

import t_explosion_source_screen as t
from grammar_search import nodes

a, z, s = t.a, t.z, t.s
OUT = Path(__file__).parent / 'fused_d_source'


def erase(tree, lo, hi):
    # Erasing a concatenation of closed structured fragments preserves the
    # outside control-flow boundaries.  The changed axiom output is separately
    # specified by the postfix macro word below.
    cc = a.chunks(tree, lo, hi)
    assert cc
    def visit(n, start=0):
        end = start + len(z.flat(n))
        if end <= lo or start >= hi:
            return n
        if lo <= start and end <= hi:
            return None
        left = visit(n[0], start)
        right = visit(n[1], start + len(z.flat(n[0])))
        return right if left is None else left if right is None else (left, right)
    new = visit(tree)
    assert z.flat(new) == z.flat(tree)[:lo] + z.flat(tree)[hi:]
    return new


def main():
    OUT.mkdir(exist_ok=True)
    evaluate, model = t.hardware.model(t.TABLE, t.OLD, t.ENGINE)
    assert evaluate(t.OLD)['cost_lower_bound'] == 219
    pushes = [z.MACRO[k] for k in (166, 121, 168)]
    original_chunks = a.chunks(t.OLD, 895, 1178)
    assert len(original_chunks) == 3
    old_atoms = [pushes[0], pushes[0], pushes[2], z.MACRO[180],
                 z.MACRO[218], z.MACRO[180], z.MACRO[218],
                 pushes[2], z.MACRO[119]]
    assert tuple(x for atom in old_atoms for x in z.flat(atom)) == z.flat(t.OLD)[895:1178]
    records, best = [], 10**9

    def consider(new, record):
        nonlocal best
        live = nodes(new)
        fixed = set().union(*(model['node_states'].get(n, ()) for n in live))
        fresh = [n for n in live if not s.leaf(n) and n not in model['node_states']]
        bare = model['nondecoder'] + len(fixed) + len(fresh)
        record.update(metrics=s.metrics(new), bare_cost=bare)
        if bare <= best:
            record.update(evaluate(new))
            if record['cost_lower_bound'] < best:
                best = record['cost_lower_bound']
                destination = OUT / f'best{best}.sites.json'
                sites = s.sites(new)
                assert s.graph_arithmetic(sites)[0] == s.graph_intervals(sites)
                destination.write_bytes(s.compact(sites))
                record['source'] = str(destination.relative_to(t.ROOT))
                print('BEST', json.dumps(record), flush=True)
        else:
            record['screened_out_by_bare_lower_bound'] = True
        records.append(record)

    exact = erase(erase(t.OLD, 1049, 1078), 895, 921)
    exact_atoms = [pushes[0], pushes[2], z.MACRO[180], z.MACRO[218],
                   z.MACRO[218], pushes[2], z.MACRO[119]]
    assert z.flat(exact) == z.flat(t.OLD)[:895] + tuple(x for atom in exact_atoms for x in z.flat(atom)) + z.flat(t.OLD)[1178:]
    assert len(z.flat(exact)) == 4689
    consider(exact, dict(layout='exact_two_deletions', binder=0, matrix=2,
                         erased_original_intervals=[[895, 921], [1049, 1078]]))

    for binder, matrix in itertools.permutations(range(3), 2):
        atoms = [pushes[binder], pushes[matrix], z.MACRO[180],
                 z.MACRO[218], z.MACRO[218], pushes[matrix], z.MACRO[119]]
        for insert_last in (False, True):
            new = a.splice(t.OLD, 895, 1178, z.seq(atoms), insert_last)
            consider(new, dict(layout='whole', binder=binder, matrix=matrix,
                               insert_last=insert_last))
        for cut1, cut2 in itertools.combinations(range(1, len(atoms)), 2):
            pieces = [z.seq(atoms[:cut1]), z.seq(atoms[cut1:cut2]), z.seq(atoms[cut2:])]
            new = t.OLD
            for (lo, hi, old_piece), piece in reversed(list(zip(original_chunks, pieces))):
                new = a.splice(new, lo, hi, piece)
            assert len(z.flat(new)) == 4689
            consider(new, dict(layout='three_chunks', binder=binder, matrix=matrix,
                               cuts=[cut1, cut2]))

    result = dict(status='UNCALIBRATED_SOURCE_SCREEN_ONLY', layouts=len(records),
                  old_row_leaves=283, replacement_row_leaves=228,
                  old_total_leaves=4744, new_total_leaves=4689,
                  minimum_hardware_lower_bound=best,
                  minimum_DAG=min(x['metrics']['dag_nodes'] for x in records),
                  full_objective_evaluations=sum('cost_lower_bound' in x for x in records),
                  calibration='OPEN: D is equivalent to T+EXP, whose Con(ZFC) calibration is unproved.',
                  hardware='Exploratory preserved-row lower bound; not a literal-machine certificate.',
                  records=records)
    (OUT / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print('DONE', json.dumps({k: v for k, v in result.items() if k != 'records'}), flush=True)


if __name__ == '__main__':
    main()
