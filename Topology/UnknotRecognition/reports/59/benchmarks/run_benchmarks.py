"""Controlled local A/A/B/C measurements; no whole-knot timing claim."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from sparse_ports import recover, certificate_queries, certificate_payload, verify_payload
from sparse_ports.intervals import IntervalOracle, dense_reference
from tests.aht_reference import count_orbits, periodic_histogram


def cases():
    n=1<<500
    for r in (8,10,12):
        yield f'coincident-{r}',n,[],[[(5,n-7)]]*r,'paired'
        yield f'disjoint-{r}',n,[],[[(5*i+1,5*i+3)] for i in range(r)],'paired'
    for r in (6,8):
        p=(1<<250)+37;n=p*((1<<250)+1)
        ports=[[(i*p//(r+1),(i+2)*p//(r+1))] for i in range(r)]
        yield f'periodic-{r}',n,[(0,n-p-1,p,n-1,1)],ports,'paired'
    r=6;n=1<<r
    ports=[]
    for i in range(r):
        stride=1<<i
        ports.append([(a,a+stride) for a in range(stride,n,2*stride)])
    yield 'full-support-6',n,[],ports,'paired'
    for r in (32,128,1024):
        n=1<<4000
        yield f'capacity-coincident-{r}',n,[],[[(5,n-7)]]*r,'capacity'


def perform(n,rows,ports,arm):
    oracle=IntervalOracle(n,ports,lambda extra:count_orbits(n,rows+extra))
    if arm.startswith('dense'):
        output=dense_reference(oracle);logical=1<<len(ports)
    else:
        found=recover(len(ports),oracle.total,oracle,
                      strategy='linear' if arm=='linear' else 'split')
        output=found.as_dict();logical=found.oracle_requests
    return output,{'orbit_calls':oracle.calls,'zeta_requests':logical,
                   'union_cache_hits':oracle.cache_hits,'support':len(output)}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--rounds',type=int,default=7)
    parser.add_argument('--output',default=str(ROOT/'results/benchmarks.json'))
    args=parser.parse_args()
    if args.rounds<1:parser.error('rounds must be positive')
    rng=random.Random(261008505)
    results=[]
    for name,n,rows,ports,scope in cases():
        # Baseline correctness independent of AHT: all components are residues.
        period=n if not rows else rows[0][2]-rows[0][0]
        expected=periodic_histogram(period,ports)
        arms=['dense-A','dense-B','split','linear'] if scope=='paired' else ['split']
        samples=[]
        for round_index in range(-1,args.rounds):
            order=list(arms);rng.shuffle(order)
            for arm in order:
                start=time.perf_counter_ns()
                output,stats=perform(n,rows,ports,arm)
                elapsed=time.perf_counter_ns()-start
                if output!=expected:raise AssertionError((name,arm,'histogram mismatch'))
                samples.append({'round':round_index,'arm':arm,
                                'nanoseconds':elapsed,**stats})
        medians={arm:statistics.median(x['nanoseconds'] for x in samples
                                      if x['arm']==arm and x['round']>=0)/1e6
                 for arm in arms}
        if scope=='paired':
            ratios={arm:statistics.median(
                next(x['nanoseconds'] for x in samples if x['round']==j and x['arm']=='dense-A') /
                next(x['nanoseconds'] for x in samples if x['round']==j and x['arm']==arm)
                for j in range(args.rounds)) for arm in ('dense-B','split','linear')}
        else:ratios={}
        entry={'name':name,'scope':scope,'ports':len(ports),'input_size_bits':n.bit_length(),
               'pairings':len(rows),'marked_intervals':sum(map(len,ports)),
               'support':len(expected),'median_ms':medians,'paired_ratios':ratios,
               'samples':samples}
        results.append(entry)
        print(name,medians,ratios,flush=True)
    # Certificate query accounting (algebraic verifier, not native local traces).
    capacities=[]
    for r in (32,128,1024):
        n=1<<4000;ports=[[(5,n-7)]]*r
        oracle=IntervalOracle(n,ports,lambda extra:count_orbits(n,extra))
        found=recover(r,n,oracle)
        before=oracle.calls
        probes=certificate_queries(found)
        for u in probes:oracle(u)
        assert verify_payload(r,n,certificate_payload(found),oracle)
        capacities.append({'r':r,'support':len(found.entries),
                           'discovery_orbit_calls':before,
                           'after_algebra_verification_calls':oracle.calls,
                           'certificate_masks':len(probes),
                           'discovery_requests':found.oracle_requests})
    record={'seed':261008505,'rounds':args.rounds,'warmup_rounds':1,
            'python':sys.version,'platform':platform.platform(),
            'scope':'local audit extraction; no maintained-suite or whole-knot timings',
            'sources':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                       for p in sorted((ROOT/'sparse_ports').glob('*.py'))},
            'cases':results,'capacity_certificates':capacities}
    Path(args.output).write_text(json.dumps(record,indent=2)+'\n')

if __name__=='__main__':main()
