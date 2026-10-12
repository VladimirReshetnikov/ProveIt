"""Pinned native audits and certified timings for adaptive periodic closure."""
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
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT));sys.path.insert(0,str(ROOT/'tests'))
from primitive_power_research import forests as harness
from fastunknot import interval_orbits as current
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.integer_codec import json_safe
from fastunknot.normal_surface_geometry import normal_arc_pairings
from normal_orbit_research.fixtures import layered_torus
from test_interval_merge_queue import random_system, literal_count, five_cycle_system
BASELINE='109dabf896f2deba143f31f68f39811b6dd3a30d';SEED=261009046
CORPUS=ROOT.parent/'reports/53/results/normal_audit_20261009_corpus.json'


def sources():
    paths=list(ROOT.rglob('*.py'))+[CORPUS]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def encode(c):return json.dumps(json_safe(c),sort_keys=True,separators=(',',':')).encode()


def rows(pairs):return [(p.a,p.b,p.c,p.d,p.reverse) for p in pairs]


def audit(old):
    rng=random.Random(SEED);records=[];comparisons=replays=0
    for case in range(1500):
        n,pairs=random_system(rng)
        expected=literal_count(n,pairs);prior_pairs=[old.IntervalPairing(*r) for r in rows(pairs)]
        for rule in ('fine_wilf','aht'):
            prior=old.count_orbits(n,prior_pairs,periodic_rule=rule,record_certificate=True)
            assert prior.complete and prior.orbits==expected
            assert verify_orbit_certificate(n,pairs,prior.certificate);replays+=1
            for scheduler in ('legacy','adaptive','queue'):
                answer=current.count_orbits(n,pairs,periodic_rule=rule,merger_scheduler=scheduler,record_certificate=True)
                assert answer.complete and answer.orbits==expected and answer.cycles==prior.cycles
                assert answer.certificate==prior.certificate
                assert all(answer.stats[k]==v for k,v in prior.stats.items() if k!='pair_tests')
                assert verify_orbit_certificate(n,pairs,answer.certificate);comparisons+=1;replays+=1
        if case<30:records.append(dict(n=n,pairings=rows(pairs),expected=expected))
    for m,bits in ((2,0),(8,0),(32,0),(16,4096)):
        n,pairs=five_cycle_system(m,None if not bits else (1<<bits)+10*m)
        prior=old.count_orbits(n,[old.IntervalPairing(*r) for r in rows(pairs)],record_certificate=True)
        assert prior.complete and prior.orbits==1 and prior.cycles==5
        assert prior.stats['pair_tests']==m**3+(m*m+5*m)//2-4
        for scheduler in ('adaptive','queue'):
            answer=current.count_orbits(n,pairs,merger_scheduler=scheduler,record_certificate=True)
            assert answer.certificate==prior.certificate and answer.cycles==5
            assert verify_orbit_certificate(n,pairs,answer.certificate)
            if scheduler=='queue':assert answer.stats['pair_tests']==5*m*m-6*m+2
        records.append(dict(m=m,bits=bits,five_cycle_exact=True))
    from weighted_research.normal_audit import run_audit
    normal=run_audit(json.loads(CORPUS.read_text()),ROOT);assert not normal['failures']
    return dict(random_systems=1500,periodic_rules=2,old_new_trace_comparisons=comparisons,random_independent_replays=replays,large_exact_cases=4,sample_sources=records,normal=normal,
        scope='Unchanged pinned producer versus all three new schedules under both periodic rules; small literal connectivity, complete certificates and every non-scheduler statistic agree. Native weighted normal APIs rerun against the frozen independent Regina corpus.')


def interval_cases():
    cases=[]
    for m in (8,16,32,64,128):
        n,pairs=five_cycle_system(m);cases.append(dict(name=f'five-cycle-{m}',family='five-cycle',parameter=m,n=n,rows=rows(pairs),expected=1))
    for k in (16,64,256):cases.append(dict(name=f'duplicates-{k}',family='duplicates',parameter=k,n=16,rows=[(0,7,8,15,False)]*k,expected=8))
    for t in (16,64,128):
        tri,vector=layered_torus(t);n,pairs=normal_arc_pairings(tri,vector)
        cases.append(dict(name=f'meridian-{t}',family='native-meridian',parameter=t,n=n,rows=rows(pairs),expected=1))
    for bits in (64,1024,4096):
        n,pairs=five_cycle_system(16,(1<<bits)+160);cases.append(dict(name=f'binary-{bits}',family='binary',parameter=bits,n=n,rows=rows(pairs),expected=1))
    return cases


def normal_cases():
    cases=[]
    for mode in ('disk','coordinates'):
        for t in (16,64,128):
            tri,vector=layered_torus(t);cases.append(dict(name=f'{mode}-{t}',mode=mode,parameter=t,triangulation=tri,coordinates=vector,expected=1))
    for bits in (64,4096,32768):
        tri,vector=layered_torus(16);g=1<<bits
        vector=[[g*x+(g+1 if j<4 else 0) for j,x in enumerate(row)] for row in vector]
        cases.append(dict(name=f'core-{bits}',mode='core',parameter=bits,triangulation=tri,coordinates=vector,expected=g))
    return cases


def benchmark(old,package,mode):
    rng=random.Random(SEED+1);records=[];proofs={}
    base=('old','adaptive','queue') if mode=='intervals' else ('old','current')
    arms=[a+s for a in base for s in ('','_AA')]
    cases=interval_cases() if mode=='intervals' else normal_cases()
    methods={}
    if mode=='normal':
        for label,prefix in (('old',package.__name__),('current','fastunknot')):
            census=importlib.import_module(prefix+'.normal_surface_components');check=importlib.import_module(prefix+'.normal_component_verify');core=importlib.import_module(prefix+'.normal_disk_kernel')
            methods[label]=(census.normal_component_census,check.verify_normal_component_certificate,core.normal_compressing_disk_count,core.verify_normal_disk_count_certificate)
    for source in cases:
        samples=[];warmups=[];reference=None
        for iteration in range(-1,5):
            order=list(arms);rng.shuffle(order);measurements={}
            for arm in order:
                label=arm.removesuffix('_AA');begin=time.perf_counter()
                if mode=='intervals':
                    module=old if label=='old' else current;pairs=[module.IntervalPairing(*r) for r in source['rows']]
                    options={} if label=='old' else dict(merger_scheduler=label)
                    answer=module.count_orbits(source['n'],pairs,record_certificate=True,**options)
                    produced=time.perf_counter()
                    assert answer.complete and answer.orbits==source['expected']
                    # The checker is unchanged; give it the public native input type.
                    verify_pairs=[current.IntervalPairing(*r) for r in source['rows']]
                    assert verify_orbit_certificate(source['n'],verify_pairs,answer.certificate)
                    end=time.perf_counter();cert=answer.certificate;stats=answer.stats
                    extra=dict(cycles=answer.cycles)
                else:
                    census,verify,core,verify_core=methods[label]
                    if source['mode']=='core':fn,checker,options=core,verify_core,{}
                    else:fn,checker,options=census,verify,dict(mode=source['mode'])
                    answer=fn(source['triangulation'],source['coordinates'],record_certificate=True,**options)
                    produced=time.perf_counter();assert answer['status']=='COMPLETE' and answer['compressing_disk_components']==source['expected']
                    assert checker(source['triangulation'],source['coordinates'],answer['certificate'])
                    end=time.perf_counter();cert=answer['certificate'];stats=answer['stats'];extra={}
                raw=encode(cert);key=sha256(raw).hexdigest();proofs[key]=cert
                if reference is None:reference=cert
                assert cert==reference
                measurements[arm]=dict(seconds=end-begin,produce_seconds=produced-begin,verify_seconds=end-produced,completed=True,certificate_sha256=key,certificate_bytes=len(raw),stats=stats,**extra)
            (warmups if iteration<0 else samples).append(dict(order=order,measurements=measurements))
        m={a:median(s['measurements'][a]['seconds'] for s in samples) for a in arms}
        pairs=[(a,'old',a) for a in base if a!='old']+[(a+'_AA',a,a+'_AA') for a in base]
        q=harness.ratios(samples,pairs);records.append(dict(source=source,samples=samples,warmups=warmups,medians=m,paired_ratios=q));print(source['name'],q,flush=True)
    return dict(cases=records,certificates=proofs,measured_calls=len(cases)*5*len(arms),warmup_calls=len(cases)*len(arms),completed_calls=len(cases)*5*len(arms),
        scope=('Complete interval counting with fresh pairing construction, certificate generation and independent replay. Native arc geometry is preconstructed outside these timers.' if mode=='intervals' else 'Complete original normal-component or quadrilateral-core query with fresh source geometry validation, certificate generation and independent replay. Exact same query and proof on both pinned old and native engines.')+' Five shuffled rounds and retained warm-ups; A/A copy of every arm. Serialization and cross-arm certificate equality checks are outside timers. No whole-knot timing.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','intervals','normal'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    harness.BASELINE=BASELINE;before=sources();begin=time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='unknot-adaptive-merger-') as directory:
        package,search,group,hashes=harness.baseline(directory)
        changed={name for name,h in hashes.items() if h!=sha256((ROOT/'fastunknot'/name).read_bytes()).hexdigest()}
        assert changed=={'interval_orbits.py'},changed
        old=importlib.import_module(package.__name__+'.interval_orbits')
        result=audit(old) if args.mode=='audit' else benchmark(old,package,args.mode)
    assert before==sources()
    result.update(mode=args.mode,baseline_commit=BASELINE,baseline_source_sha256=hashes,source_sha256=before,source_hashes_unchanged=True,seconds=time.perf_counter()-begin,seed=SEED,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('cases','certificates','source_sha256','baseline_source_sha256','normal','sample_sources')},indent=2))


if __name__=='__main__':main()
