"""Fresh-state paired same-kernel measurements; raw observations, not knot timings."""
import argparse
from hashlib import sha256
import platform
import random
from statistics import median
import time
from common import ROOT,parallel_chain,literal
from sparse_incidence.api import analyze,dense_ablation
from sparse_incidence.verify import verify
from sparse_incidence.codec import save,dumps


def make_cases():
    cases=[]
    n=1 << 4000;r=8
    for shape in ('coincident','nested','disjoint'):
        ports=([[(0,n//2)]]*r if shape=='coincident' else
               [[(0,(i+1)*n//r)] for i in range(r)] if shape=='nested' else
               [[(i*n//r,(i+1)*n//r)] for i in range(r)])
        cases.append(('static4000_'+shape,(n,[],ports)))
    for shape in ('coincident','nested','disjoint'):
        cases.append(('chain8_500_'+shape,parallel_chain(1 << 500,8,6,shape)))
    cases.append(('chain16_128_disjoint',parallel_chain(1 << 128,16,8)))
    # A dense abstract-incidence control: bit pattern m is the signature of point m.
    # Its interval input grows exponentially with r; it is not a compact hard family.
    r=5;n=1 << r
    ports=[[(m,m+1) for m in range(n) if (m >> bit)&1] for bit in range(r)]
    cases.append(('all_signatures_r5',(n,[],ports)))
    cases.append(('small_mixed',(10,[[0,4,5,9,1]],
                               [[(0,2)],[(6,9)],[(0,1),(9,10)]])))
    return cases


def benchmark_case(name,case,rng,rounds):
    expected=dict(dense_ablation(*case)['histogram'])
    def dense():return dense_ablation(*case)
    def flat():return analyze(*case,strategy='flat')
    def balanced():return analyze(*case)
    def certified():
        result=analyze(*case,record_certificate=True)
        if not verify(*case,result['certificate']):raise AssertionError('replay failed')
        return result
    arms=dict(dense=dense,dense_AA=dense,flat=flat,balanced=balanced,
              certified_replay=certified)
    samples={a:[] for a in arms};orders=[];stats={}
    for trial in range(-1,rounds):
        order=list(arms);rng.shuffle(order);orders.append(order)
        for arm in order:
            start=time.perf_counter_ns();result=arms[arm]()
            elapsed=(time.perf_counter_ns()-start)/1e9
            if dict(result['histogram']) != expected:raise AssertionError((name,arm))
            stats[arm]=result['stats']
            if trial >= 0:samples[arm].append(elapsed)
    proof=analyze(*case,record_certificate=True)['certificate']
    return dict(name=name,size=case[0],size_bits=case[0].bit_length(),
                pairings=case[1],ports=case[2],support=len(expected),
                seconds=samples,orders=orders,stats=stats,
                medians={a:median(v) for a,v in samples.items()},
                paired_dense_over={a:median(x/y for x,y in zip(samples['dense'],v))
                                   for a,v in samples.items()},
                certificate_bytes=len(dumps(proof).encode()),
                certificate_union_proofs=len(proof['union_proofs']))


def scaling(rng,rounds):
    rows=[]
    for rank in (16,32,64,128):
        n=1 << 500
        ports=[[(i*n//rank,(i+1)*n//rank)] for i in range(rank)]
        samples=[];last=None
        for _ in range(rounds):
            start=time.perf_counter_ns();last=analyze(n,[],ports)
            samples.append((time.perf_counter_ns()-start)/1e9)
        expected={1 << i:(i+1)*n//rank-i*n//rank for i in range(rank)}
        if dict(last['histogram']) != expected:raise AssertionError('scaling mismatch')
        rows.append(dict(name='disjoint_static',rank=rank,size_bits=n.bit_length(),
                         dense_entries=1 << rank,sparse_entries=len(expected),
                         seconds=samples,median=median(samples),stats=last['stats']))
    for rank in (64,256,1024):
        n=1 << 16000
        ports=[[] for _ in range(rank)];ports[rank//3]=[(0,n)]
        samples=[]
        for _ in range(rounds):
            start=time.perf_counter_ns();last=analyze(n,[],ports)
            samples.append((time.perf_counter_ns()-start)/1e9)
        if last['histogram'] != [[1 << (rank//3),n]]:raise AssertionError('singleton mismatch')
        rows.append(dict(name='one_active_port',rank=rank,size_bits=n.bit_length(),
                         dense_entries=1 << rank,sparse_entries=1,
                         seconds=samples,median=median(samples),stats=last['stats']))
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rounds',type=int,default=7)
    parser.add_argument('--output',default=str(ROOT/'results/benchmark.json'))
    args=parser.parse_args()
    if args.rounds < 1:parser.error('rounds must be positive')
    rng=random.Random(261008491)
    data=dict(schema='sparse-incidence-benchmark-v1',seed=261008491,
              rounds=args.rounds,warmups=1,python=platform.python_version(),
              platform=platform.platform(),
              scope='Supplied interval relations. Same unchanged upstream AHT kernel, classical periodic rule, in all arms. '
                    'Dense arm is a controlled research ablation; no whole-recognizer or native '
                    'normal-surface benchmark was performed.',cases=[],
              sources={str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
                       for folder in ('src','vendor','experiments')
                       for p in (ROOT/folder).rglob('*.py')})
    for name,case in make_cases():
        row=benchmark_case(name,case,rng,args.rounds);data['cases'].append(row)
        print(name,{k:round(v*1000,3) for k,v in row['medians'].items()},flush=True)
    data['scaling']=scaling(rng,args.rounds)
    save(args.output,data)

if __name__=='__main__':main()
