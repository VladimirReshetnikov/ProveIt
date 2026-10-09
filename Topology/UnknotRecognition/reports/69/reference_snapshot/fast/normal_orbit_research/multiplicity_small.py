"""Batched follow-up for small multiplicities, including unchanged-baseline controls."""
import argparse
import hashlib
import json
from pathlib import Path
import random
import statistics
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from normal_orbit_research.multiplicity import (
    BASELINE, pinned, sources, topology, proof_bytes, layered_torus,
    normal_surface_topology,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    before = sources()
    own_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    old, _, old_hashes = pinned()
    rng = random.Random(261008499)
    tri, disk = layered_torus(1)
    cases = [('disk1', tri, disk), ('one_sided1', tri, [[0,0,0,0,0,1,0]]),
             ('mixed1', tri, [[1,1,1,1,0,1,0]]), ('disk8', *layered_torus(8))]
    arms = ('old', 'control', 'current', 'unreduced')
    rows = []; start_all = time.perf_counter()
    for name, tri, base in cases:
        for k in (2, 3, 8, 64, 2**32):
            vector = [[k*v for v in row] for row in base]
            original = old.normal_surface_topology(tri, vector, record_certificate=True)
            current = normal_surface_topology(tri, vector, record_certificate=True)
            expected = topology(original)
            warmups, samples = [], []
            for round_id in range(-1, 7):
                order = list(arms); rng.shuffle(order); times = {}
                for arm in order:
                    start = time.perf_counter()
                    for _ in range(10):
                        result = (old.normal_surface_topology(tri, vector) if arm in ('old', 'control')
                                  else normal_surface_topology(tri, vector, reduce_multiplicity=arm != 'unreduced'))
                    times[arm] = (time.perf_counter()-start)/10
                    assert topology(result)==expected
                (warmups if round_id<0 else samples).append(dict(order=order, seconds=times))
            medians = {arm:statistics.median(s['seconds'][arm] for s in samples) for arm in arms}
            ratios = {arm:statistics.median(s['seconds']['old']/s['seconds'][arm] for s in samples)
                      for arm in ('control','current','unreduced')}
            row = dict(family=name, scale=k, medians=medians, paired_ratios=ratios,
                samples=samples, warmups=warmups, old_cycles=original['cycles'],new_cycles=current['cycles'],
                old_proof_bytes=proof_bytes(original['certificate']),new_proof_bytes=proof_bytes(current['certificate']),
                new_with_old_cycle_cap=normal_surface_topology(tri, vector,max_cycles=original['cycles'])['status'])
            rows.append(row)
            print(name,k,json.dumps(dict(ratios=ratios,old_cycles=row['old_cycles'],new_cycles=row['new_cycles'])),flush=True)
    assert sources()==before
    result=dict(seed=261008499,baseline_commit=BASELINE,baseline_source_sha256=old_hashes,
                source_sha256=before,driver_sha256=own_hash,source_hashes_unchanged=True,
                seconds=time.perf_counter()-start_all,rounds=7,excluded_warmups=1,batch=10,cases=rows,
                scope='Small complete topology calls; count-only with fresh validation. Old/control are identical pinned code. Cycle-cap probe is correctness evidence, outside timing.')
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__': main()
