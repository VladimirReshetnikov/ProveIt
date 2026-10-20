#!/usr/bin/env python3
"""Uncalibrated T + explicit explosion source layouts against literal K219.

These are source/layout experiments only. No equiconsistency theorem for
this replacement has been established, and the hardware objective is not
a compiled-machine certificate.
"""
import itertools
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'theory_notes'))
import a10_source_search as a
sys.path.insert(0, str(ROOT / 'source218'))
import hardware_objective219 as hardware

z, s, b = a.z, a.s, a.b
BASE = ROOT / 'baseline219/K219_Construction_2026-10-20/machine'
OLD = s.tree(json.loads((BASE / 'sites219.json').read_text()))
TABLE = b.read_table((BASE / 'k219.native.tm').read_bytes())
ENGINE = json.loads((ROOT / 'source218/frozen_engine_rows219.json').read_text())['rows']
OUT = Path(__file__).parent / 't_explosion_source'


def main():
    OUT.mkdir(exist_ok=True)
    evaluate, model = hardware.model(TABLE, OLD, ENGINE)
    baseline = evaluate(OLD)
    assert baseline['cost_lower_bound'] == 219 and baseline['context_penalty'] == 0
    original_chunks = a.chunks(OLD, 895, 1178)
    pushes = [z.MACRO[k] for k in (166, 121, 168)]
    records = []
    for binder, matrix in itertools.permutations(range(3), 2):
        t_atoms = [pushes[binder], pushes[matrix], z.MACRO[180],
                   pushes[matrix], z.MACRO[119]]
        for explosion_matrix in range(3):
            e_atoms = [z.MACRO[177], pushes[explosion_matrix], z.MACRO[119]]
            for reverse, insert_last in itertools.product((False, True), repeat=2):
                atoms = e_atoms + t_atoms if reverse else t_atoms + e_atoms
                replacement = z.seq(atoms)
                assert len(z.flat(replacement)) == 207
                new = a.splice(OLD, 895, 1178, replacement, insert_last)
                assert len(z.flat(new)) == 4668
                sites = s.sites(new)
                assert s.graph_arithmetic(sites)[0] == s.graph_intervals(sites)
                receipt = evaluate(new)
                receipt.update(binder=binder, matrix=matrix,
                               explosion_matrix=explosion_matrix,
                               explosion_first=reverse, insert_last=insert_last)
                records.append(receipt)
    records.sort(key=lambda x: (x['cost_lower_bound'], x['context_penalty'],
                               x['metrics']['dag_nodes']))
    for index, record in enumerate(records[:12]):
        binder, matrix, em = record['binder'], record['matrix'], record['explosion_matrix']
        tt = [pushes[binder], pushes[matrix], z.MACRO[180], pushes[matrix], z.MACRO[119]]
        ee = [z.MACRO[177], pushes[em], z.MACRO[119]]
        new = a.splice(OLD, 895, 1178, z.seq(ee + tt if record['explosion_first'] else tt + ee),
                       record['insert_last'])
        destination = OUT / f'candidate{index:02d}.sites.json'
        destination.write_bytes(s.compact(s.sites(new)))
        record['source'] = str(destination.relative_to(ROOT))
    result = dict(status='UNCALIBRATED_SOURCE_SCREEN_ONLY', baseline=baseline,
                  old_row_leaves=283, replacement_leaves=207,
                  old_total_leaves=4744, new_total_leaves=4668,
                  original_chunk_intervals=[[lo, hi] for lo, hi, _ in original_chunks],
                  layouts=len(records), records=records,
                  calibration='UNPROVED: T plus explosion versus original seed-K consistency.',
                  hardware='Exploratory preserved-row lower bound, not a literal compiled table.')
    (OUT / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'records'}, indent=2))
    for record in records[:8]:
        print(json.dumps(record), flush=True)


if __name__ == '__main__':
    main()
