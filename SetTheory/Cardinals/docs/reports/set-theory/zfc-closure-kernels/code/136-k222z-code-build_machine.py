#!/usr/bin/env python3
"""Apply the two certified folds, canonicalize, and check the exact blank start."""
from pathlib import Path
import argparse, csv, json
import common as c
import check_folds as f

CANONICAL_SHA = '60e21a040e58e2a2840b0f3d58ad3ee0e6ef4d0d5cdf1372d5a69355f1198ca1'
LEGACY_SHA = 'cd771c40f409ebd9b86cdd5b7b7e5c6e0b03abfb423633ad45232ebd1bcadc82'

def build(source_dir, output):
    output.mkdir(parents=True, exist_ok=True)
    parent = source_dir/'parent224.k.tm'
    spec = json.loads((c.ROOT/'inputs/folds.json').read_text())
    c.need(c.sha(parent) == spec['parent_sha256'], 'Parent differs')
    table = f.read_table(parent)
    for fold in spec['folds']:
        table, _ = f.transformed(table, fold)
    candidate = output/'candidate222.k.tm'
    candidate.write_bytes(c.encode(table))
    c.need(c.sha(candidate) == c.K_SHA, 'Native candidate differs')
    receipt = f.check_chain(parent, candidate, c.ROOT/'inputs/folds.json')
    c.dump(output/'folds.json', receipt)
    (output/'parent224.k.tm').write_bytes(parent.read_bytes())
    (output/'sites.json').write_bytes((source_dir/'sites.json').read_bytes())
    _, metrics = c.source_metrics(output/'sites.json')
    c.need(len(table) == 444, 'Expected exactly 444 rows')
    canonical, labels = c.canonical(table, 0, 254)
    (output/'candidate222.tm').write_bytes(c.encode(canonical))
    c.need(c.sha(output/'candidate222.tm') == CANONICAL_SHA, 'Canonical bytes differ')
    mapfile = c.ROOT/'inputs/legacy_state_map.json'
    c.need(c.sha(mapfile) == c.MAP_SHA, 'Legacy map differs')
    old = json.loads(mapfile.read_text())
    legacy = {int(q): v for q,v in old['k230_to_old'].items()}
    legacy[254] = 254
    for q in labels:
        if q not in legacy: legacy[q] = q
    c.need(len({legacy[q] for q in labels}) == len(labels), 'Legacy labels collide')
    lt = {(legacy[q],b):(w,d,legacy[z]) for (q,b),(w,d,z) in table.items()}
    (output/'candidate222.legacy.tm').write_bytes(c.encode(lt,legacy[0]))
    c.need(c.sha(output/'candidate222.legacy.tm') == LEGACY_SHA, 'Legacy bytes differ')
    c.dump(output/'state_map.json',dict(
        canonical_order='Breadth first from start; read 0 before read 1',
        k_to_canonical=labels,k_to_legacy={q:legacy[q] for q in labels},
        canonical_start=0,canonical_halt=222,k_start=0,k_halt=254,
        legacy_start=95,legacy_dispatcher=96))
    with (output/'candidate222.csv').open('w', newline='') as stream:
        writer=csv.writer(stream)
        writer.writerow(['state','read','write','move','next'])
        writer.writerows((q,b,w,'R' if d==1 else 'L',z)
                        for (q,b),(w,d,z) in sorted(canonical.items()))
    boot=c.bootstrap(table)
    boot['canonical_state']=labels[84]
    # Independent dense-table / bytearray-tape replay, with canonical labels.
    # In T steps the head lies in [-T,T], so this finite allocation represents
    # every cell that could be visited, with the exterior identically zero.
    dense=[[canonical[q,b] for b in (0,1)] for q in range(222)]
    ticks=409835; origin=ticks
    q=0; h=origin; tape=bytearray(2*ticks+1)
    for _ in range(ticks):
        c.need(q<222,'Premature dense halt')
        w,d,q=dense[q][tape[h]]
        tape[h]=w
        h+=d
    dense_ones=[i-origin for i,b in enumerate(tape) if b]
    c.need(q==labels[84] and h-origin==boot['head'] and dense_ones==boot['one_cells'],
           'Dense and sparse complete bootstrap endpoints differ')
    boot['independent_dense_replay']=True
    boot['independent_dense_tape_storage']='bytearray, all potentially visited cells'
    c.dump(output/'bootstrap.json',boot)
    answer=dict(status='EXACT_222_STATE_BINARY_BUILD_PASS',working_states=222,
        rows=444,symbols=[0,1],start=0,halt=222,canonical_dispatcher=labels[84],
        all_working_states_graph_reachable=True,source_metrics=metrics,
        canonical_sha256=CANONICAL_SHA,native_sha256=c.K_SHA,
        legacy_sha256=LEGACY_SHA,source_sha256=c.SOURCE_SHA,
        blank_startup_steps=409835,blank_startup_head=-5,
        proof_status='Mathematical certificates; no new Rocq/Lean endpoint.')
    c.dump(output/'build.json',answer)
    return answer

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-dir',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args()
    print(json.dumps(build(a.source_dir,a.output),indent=2))
