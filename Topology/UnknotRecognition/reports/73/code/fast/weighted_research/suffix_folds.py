"""Pinned exact-output audit and complete-query timings for local fold overlays."""
import argparse
from hashlib import sha256
import importlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
import tempfile
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from primitive_power_research import forests as harness
from weighted_research import compact_coordinates as prior
from weighted_research import kernel_audit, checker_audit, normal_audit
from fastunknot import weighted_orbits
from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from normal_orbit_research.fixtures import layered_torus
BASELINE='e052c7ef07f36692496a47b0af39a5c39ab0229f';SEED=261009443


def audit(old_census, old_weights):
    kernel=kernel_audit.audit(10000,SEED)
    checker=checker_audit.run()
    corpus=json.loads(prior.CORPUS.read_text())
    normal=normal_audit.run_audit(corpus,ROOT);assert not normal['failures']
    sources={t['id']:t['triangulation'] for t in corpus['triangulations']}
    comparisons=0
    for case in corpus['cases']:
        raw=sources[case['triangulation_id']];vector=case['coordinates']
        for mode in ('disk','coordinates'):
            a=normal_component_census(raw,vector,mode=mode,record_certificate=True)
            b=old_census(raw,vector,mode=mode,record_certificate=True)
            assert a==b;comparisons+=1
    rng=random.Random(SEED+1)
    pair_type=importlib.import_module(old_weights.__package__+'.interval_orbits').IntervalPairing
    for _ in range(1000):
        size,pairs,intervals=kernel_audit.random_input(rng)
        old_pairs=[pair_type(p.a,p.b,p.c,p.d,p.reverse) for p in pairs]
        a=weighted_orbits.weighted_orbit_histogram(size,pairs,intervals,dimension=3,record_certificate=True)
        b=old_weights.weighted_orbit_histogram(size,old_pairs,intervals,dimension=3,record_certificate=True)
        assert a==b
    return dict(kernel=kernel,checker=checker,normal=normal,
                complete_normal_answer_equalities=comparisons,complete_abstract_answer_equalities=1000)


def benchmark(old_census,old_verify):
    rng=random.Random(SEED+2);records=[];proofs={}
    cases=[dict(**case,mode='coordinates') for case in prior.cases()]
    for t in (16,128):
        raw,vector=layered_torus(t)
        cases.append(dict(name=f'disk-{t}',triangulation=raw,coordinates=vector,mode='disk'))
    arms=('old','old_AA','current','current_AA')
    methods={'old':(old_census,old_verify),'current':(normal_component_census,verify_normal_component_certificate)}
    for source in cases:
        samples=[];warmups=[];reference=None
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                census,verify=methods[arm.removesuffix('_AA')]
                raw,vector=source['triangulation'],source['coordinates'];begin=time.perf_counter()
                answer=census(raw,vector,mode=source['mode'],record_certificate=True)
                middle=time.perf_counter();assert answer['status']=='COMPLETE'
                assert verify(raw,vector,answer['certificate']);end=time.perf_counter()
                if reference is None:reference=answer
                assert answer==reference
                cert=answer['certificate'];encoded=prior.encode(cert);key=sha256(encoded).hexdigest();proofs[key]=cert
                measurements[arm]=dict(seconds=end-begin,produce_seconds=middle-begin,verify_seconds=end-middle,
                    completed=True,certificate_sha256=key,certificate_bytes=len(encoded),stats=answer['stats'])
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        medians={a:median(s['measurements'][a]['seconds'] for s in samples) for a in arms}
        ratios={f'{a}/{b}':median(s['measurements'][a]['seconds']/s['measurements'][b]['seconds'] for s in samples)
                for a,b in (('old','current'),('old','old_AA'),('current','current_AA'))}
        records.append(dict(source=source,samples=samples,warmups=warmups,medians=medians,paired_ratios=ratios))
        print(source['name'],ratios,flush=True)
    return dict(cases=records,certificates=proofs,measured_calls=len(records)*20,warmup_calls=len(records)*4,
        completed_calls=len(records)*20,scope='Complete native normal census, certificate and independent replay. '
        'Identical output, proof and statistics on both engines. Five shuffled rounds with A/A controls, retained '
        'warm-ups. Source construction and serialization outside timers. Supplied surfaces only.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','benchmark'))
    p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=prior.sources();harness.BASELINE=BASELINE;start=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-suffix-fold-') as directory:
        package,_,_,hashes=harness.baseline(directory)
        changed={name for name,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/name).read_bytes()).hexdigest()}
        assert changed=={'weighted_orbits.py'},changed
        old_census=importlib.import_module(package.__name__+'.normal_surface_components').normal_component_census
        old_verify=importlib.import_module(package.__name__+'.normal_component_verify').verify_normal_component_certificate
        old_weights=importlib.import_module(package.__name__+'.weighted_orbits')
        result=audit(old_census,old_weights) if args.mode=='audit' else benchmark(old_census,old_verify)
    assert prior.sources()==before
    result.update(mode=args.mode,baseline_commit=BASELINE,source_sha256=before,baseline_source_sha256=hashes,
        source_hashes_unchanged=True,seed=SEED,seconds=time.perf_counter()-start,
        python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n');print('complete',args.mode,result['seconds'],flush=True)


if __name__=='__main__':main()
