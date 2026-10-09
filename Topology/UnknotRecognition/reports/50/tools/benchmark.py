"""Shuffled native-kernel comparisons; outputs every sample, not just ratios."""
from bootstrap import bootstrap, PINS
ROOT=bootstrap()
from fastunknot.interval_orbits import IntervalPairing as P, SignedPairing as SP, signed_cover
from fastunknot.interval_incidence import analyze_port_incidence as dense
from fastunknot.interval_incidence import verify_port_incidence_certificate as dense_verify
from fastunknot.sparse_incidence import analyze_sparse_port_incidence as sparse
from fastunknot.sparse_incidence import analyze_sparse_signed_incidence as signed
from fastunknot.sparse_incidence_verify import verify_sparse_port_incidence_certificate as verify
from fastunknot.sparse_incidence_verify import verify_sparse_signed_incidence_certificate as signed_verify
from fastunknot.integer_codec import json_safe
import argparse, hashlib, json, platform, random, statistics, sys, time


def fixtures():
    L=1<<256
    out=[]
    for r in (6,8,10):
        out.append((f'static-disjoint-{r}',(r+2)*L,[],[[(i*L,(i+1)*L)] for i in range(r)]))
    for r in (4,10):
        out.append((f'coincident-{r}',8*L,[],[[(L,3*L)]]*r))
    r=10
    out.append(('nested-10',12*L,[],[[(0,(i+1)*L)] for i in range(r)]))
    r=8
    # A genuine binary interval relation, not expanded vertices.
    ps=[P(0,L-1,L,2*L-1),P(2*L,3*L-1,3*L,4*L-1,True)]
    step=L//8
    ports=[[(i*step,(i+1)*step)] for i in range(r)]
    out.append(('paired-blocks-8',4*L,ps,ports))
    r=6; n=1<<r
    ports=[[(x,x+1) for x in range(n) if x>>i&1] for i in range(r)]
    out.append(('all-signatures-6',n,[],ports))
    return out


def enc(obj):
    return json.dumps(json_safe(obj),sort_keys=True,separators=(',',':')).encode()


def digest(hist):
    return hashlib.sha256(enc(sorted(hist.items()))).hexdigest()


def measure_case(case, rng, rounds, repeats):
    name,n,ps,ports=case
    r=len(ports)
    arms=('dense','linear','split','split_control','split_certified')
    def run(arm):
        if arm=='dense': return dense(n,ps,ports,max_ports=r)
        cert=(arm=='split_certified')
        x=sparse(n,ps,ports,strategy='linear' if arm=='linear' else 'split',record_certificate=cert)
        if cert:
            assert verify(n,ps,ports,x['certificate'])
        return x
    expected={i:w for i,w in enumerate(dense(n,ps,ports,max_ports=r)['histogram']) if w}
    samples={a:[] for a in arms}; stats={}; cert_sizes={}
    orders=[]
    for round_no in range(-1,rounds):
        order=list(arms);rng.shuffle(order);orders.append(order)
        for arm in order:
            start=time.perf_counter_ns()
            for _ in range(repeats): x=run(arm)
            elapsed=(time.perf_counter_ns()-start)/1e6/repeats
            assert x['status']=='COMPLETE'
            got=({i:w for i,w in enumerate(x['histogram']) if w} if arm=='dense' else dict(x['histogram']))
            assert got==expected,(name,arm)
            stats[arm]=x['stats']
            if 'certificate' in x: cert_sizes[arm]=len(enc(x['certificate']))
            if round_no>=0:samples[arm].append(elapsed)
    # Produce both certificates outside timings for size and independent validation.
    dc=dense(n,ps,ports,max_ports=r,record_certificate=True)
    assert dense_verify(n,ps,ports,dc['certificate'],max_ports=r)
    cert_sizes['dense']=len(enc(dc['certificate']))
    med={a:statistics.median(v) for a,v in samples.items()}
    ratios={a:statistics.median(d/s for d,s in zip(samples['dense'],samples[a])) for a in arms if a!='dense'}
    return dict(name=name,size_bits=n.bit_length(),r=r,k=len(ps),M=sum(map(len,ports)),s=len(expected),
                dense_slots=1<<r,output_sha256=digest(expected),repeats=repeats,
                orders_including_warmup=orders,samples_ms=samples,medians_ms=med,
                paired_dense_over_arm=ratios,stats=stats,certificate_bytes=cert_sizes)


def large_cases():
    out=[]
    for r in (32,128,256):
        n=1<<500;ps=[];ports=[[(i,i+1)] for i in range(r)]
        ts=[]
        for j in range(3):
            start=time.perf_counter_ns()
            x=sparse(n,ps,ports,strategy='split',record_certificate=True)
            assert verify(n,ps,ports,x['certificate'])
            ts.append((time.perf_counter_ns()-start)/1e6)
        expected={0:n-r,**{1<<i:1 for i in range(r)}}
        assert dict(x['histogram'])==expected
        out.append(dict(r=r,size_bits=n.bit_length(),s=r+1,samples_ms=ts,
                        median_ms=statistics.median(ts),stats=x['stats'],
                        certificate_bytes=len(enc(x['certificate'])),
                        dense_status='NOT_RUN: explicit output has 2**r slots; no timing ratio'))
    return out


def signed_cases(rng,rounds):
    out=[]
    for r in (8,16):
        L=1<<128;n=(r+1)*L
        ps=[SP(P(i*L,(i+1)*L-1,i*L,(i+1)*L-1,True),0) for i in range(r+1)]
        ps +=[SP(P(i*L,(i+1)*L-1,i*L,(i+1)*L-1),1) for i in range(0,r+1,2)]
        ports=[[(i*L,(i+1)*L)] for i in range(r)]
        cover=signed_cover(n,ps)
        lifted_ports=[p+[(a+n,b+n) for a,b in p] for p in ports]
        def reused():return signed(n,ps,ports,strategy='split')
        def double():
            b=sparse(n,[p.pairing for p in ps],ports,strategy='split')
            c=sparse(2*n,cover,lifted_ports,strategy='split')
            hd=dict(c['histogram'])
            return dict(signed_histogram=[[t,hd[t]-w,2*w-hd[t]] for t,w in b['histogram']],
                        stats=dict(orbit_queries=b['stats']['orbit_queries']+c['stats']['orbit_queries'],
                                   cover_orbit_queries=c['stats']['orbit_queries']))
        arms={'support_reuse':reused,'two_searches':double}
        samples={a:[] for a in arms};stats={}
        expected=None
        for j in range(-1,rounds):
            order=list(arms);rng.shuffle(order)
            for arm in order:
                start=time.perf_counter_ns();x=arms[arm]();dt=(time.perf_counter_ns()-start)/1e6
                got=sorted(x['signed_histogram'])
                if expected is None:expected=got
                assert got==expected
                if j>=0:samples[arm].append(dt)
                stats[arm]=x['stats']
        cert=signed(n,ps,ports,strategy='split',record_certificate=True)
        assert signed_verify(n,ps,ports,cert['certificate'])
        out.append(dict(r=r,s=len(expected),samples_ms=samples,stats=stats,
             median_ms={a:statistics.median(v) for a,v in samples.items()},
             paired_ratio=statistics.median(a/b for a,b in zip(samples['two_searches'],samples['support_reuse']))))
    return out


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',default=str(ROOT/'results/benchmark.json'))
    p.add_argument('--rounds',type=int,default=5);p.add_argument('--repeats',type=int,default=3)
    args=p.parse_args()
    if args.rounds<1 or args.repeats<1:p.error('positive rounds and repeats required')
    rng=random.Random(261008911)
    cases=[]
    for case in fixtures():
        row=measure_case(case,rng,args.rounds,args.repeats);cases.append(row)
        print(row['name'],row['s'],{k:round(v,3) for k,v in row['medians_ms'].items()},flush=True)
    result=dict(seed=261008911,python=sys.version,platform=platform.platform(),native_git_blobs=PINS,
                rounds=args.rounds,repeats=args.repeats,cases=cases,large_cases=[],
                signed_cases=[],scope='Interval subsystem only; no knot recognition dispatch')
    with open(args.output,'w') as f:json.dump(result,f,indent=2)
    result['large_cases']=large_cases()
    with open(args.output,'w') as f:json.dump(result,f,indent=2)
    result['signed_cases']=signed_cases(rng,args.rounds)
    with open(args.output,'w') as f:json.dump(result,f,indent=2)
    print('Saved',args.output,flush=True)
if __name__=='__main__':main()
