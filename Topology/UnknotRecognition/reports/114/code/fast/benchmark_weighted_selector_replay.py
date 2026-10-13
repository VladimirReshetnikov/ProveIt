"""Paired complete parallelity timings against the preserved two-pass verifier."""
import argparse
import gc
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
from types import ModuleType

from fastunknot.integer_codec import json_safe
from fastunknot.normal_parallelity import normal_cut_parallelity
import fastunknot.normal_parallelity_verify as checker
from normal_orbit_research.fixtures import layered_torus
from normal_orbit_research import seeds

BASELINE='42ca57831b1e07dea93700b457feeadc153b0e9f'
REPO=Path(__file__).resolve().parents[3]

def historical_verifier():
    modules=[];hashes={}
    for name in ('weighted_orbit_verify','weighted_transversal_verify'):
        path=f'Topology/UnknotRecognition/fast/fastunknot/{name}.py'
        source=subprocess.check_output(['git','show',f'{BASELINE}:{path}'],cwd=REPO)
        hashes[path]=sha256(source).hexdigest();module=ModuleType(f'fastunknot._historical_{name}');module.__package__='fastunknot'
        exec(compile(source,f'{BASELINE}:{path}','exec'),module.__dict__);modules.append(module)
    weighted,selector=modules
    # Bind every imported weighted helper to the historical module as well.
    for name in ('verify_weighted_orbit_certificate','_initial_weights','_canonical_pairings','_contract_weights',
                 '_translation_fold','_reflection_fold','_move_interval','_InvalidWeightedProof'):
        selector.__dict__[name]=weighted.__dict__[name]
    return selector.verify_weighted_orbit_transversal,hashes


def encode(value):return json.dumps(json_safe(value),sort_keys=True,separators=(',',':')).encode()


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
    old,old_hashes=historical_verifier();new=checker.verify_weighted_orbit_transversal;pins=seeds.sources()
    cases={}
    for t,n in ((1,4096),(4,1),(4,128),(16,1)):
        raw,base=layered_torus(t);cases[f'layered_{t}_copies_{n}']=raw,[[n*x for x in row]for row in base]
    rng=random.Random(26101210);samples=[];expected={}
    try:
        for round_number in range(6):
            tasks=[(name,arm)for name in cases for arm in ('old','old_control','new')];rng.shuffle(tasks)
            for name,arm in tasks:
                raw,rows=cases[name];checker.verify_weighted_orbit_transversal=new if arm=='new'else old
                gc.collect();began=perf_counter()
                answer=normal_cut_parallelity(raw,rows,record_certificate=True)
                assert checker.verify_normal_cut_parallelity(raw,rows,answer['certificate'])
                wire=encode(answer);elapsed=perf_counter()-began;digest=sha256(wire).hexdigest()
                assert expected.setdefault(name,digest)==digest
                samples.append(dict(case=name,arm=arm,round=round_number,warmup=round_number==0,seconds=elapsed,result_sha256=digest,result_bytes=len(wire)))
                del answer,wire
            print('selector replay timing round',round_number,flush=True)
    finally:checker.verify_weighted_orbit_transversal=new
    assert pins==seeds.sources();summary={}
    for name in cases:
        rows=[r for r in samples if r['case']==name and not r['warmup']]
        def ratio(arm):return statistics.median(next(r['seconds']for r in rows if r['arm']=='old'and r['round']==i)/next(r['seconds']for r in rows if r['arm']==arm and r['round']==i)for i in range(1,6))
        summary[name]=dict(paired_old_over_new=ratio('new'),identical_control=ratio('old_control'),
            median_seconds={arm:statistics.median(r['seconds']for r in rows if r['arm']==arm)for arm in ('old','old_control','new')})
    result=dict(native_source_sha256=pins,baseline_revision=BASELINE,baseline_source_sha256=old_hashes,python=platform.python_version(),seed=26101210,
        timing='Complete source preparation, parallelity construction, independent certificate replay and serialization. '
               'Only the selector verifier differs; historical selector and weighted verifier sources are loaded directly '
               'from the pinned Git revision. Every result is byte-identical across arms. Five shuffled paired rounds '
               'after warmup, with an identical historical control. Garbage collection and fixture construction excluded.',samples=samples,summary=summary)
    args.output.write_bytes(encode(result)+b'\n');print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
