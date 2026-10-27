"""Local microbenchmarks on EXACTLY the same coefficient and representative data.

Not an end-to-end SAT/contractor benchmark. Synthetic factors; no imported program
is executed. Baseline uses optimized Gray updates too. Timing includes all lifts,
setup, extraction, precision division and return, excludes input generation.
"""
import gc,json,platform,random,statistics,sys,time
from pathlib import Path
from packet_extraction import Ring,forward_reference,forward_gray,centered_half_gray


def main():
    rng=random.Random(202610270209)
    specs=[
        ('sqfree12_p64',12,[1]*12,Ring(64)),
        ('sqfree16_p64',16,[1]*16,Ring(64)),
        ('sqfree18_p256',18,[1]*18,Ring(256)),
        ('sqfree16_p1024',16,[1]*16,Ring(1024)),
        ('repeated_twos16_p64',16,[2]*8,Ring(64)),
        ('repeated_threes18_p256',18,[3]*6,Ring(256)),
        ('mixed16_p256',16,[1,1,2,3,4,5],Ring(256)),
        ('free_quotient_sqfree10',10,[1]*10,Ring(64,(1,1),2)),
        ('free_quotient_twos12',12,[2]*6,Ring(64,(0,0),2)),
    ]
    results=[]
    for name,R,beta,ring in specs:
        rows=[]
        for _ in range(R):
            row=[]
            for _ in beta:
                x=tuple(rng.getrandbits(ring.precision) for d in range(ring.dimension))
                row.append(x[0] if ring.scalar else x)
            rows.append(row)
        methods=[forward_gray,centered_half_gray]
        if R<=16 and ring.scalar: methods.insert(0,forward_reference)
        # One untimed correctness/warmup pass, requiring identical outputs.
        expected=None;data={}
        for fn in methods:
            stats={};value=fn(rows,beta,ring,stats)
            if expected is None:expected=value
            elif expected!=value:raise AssertionError((name,fn.__name__,'coefficient mismatch'))
            data[fn.__name__]={'seconds':[],'stats':stats}
        # Alternate ordering to avoid always favoring a later/warmed method.
        for repeat in range(3):
            order=methods if repeat%2==0 else list(reversed(methods))
            for fn in order:
                gc.collect();start=time.perf_counter();value=fn(rows,beta,ring)
                elapsed=time.perf_counter()-start
                if value!=expected:raise AssertionError('timed mismatch')
                data[fn.__name__]['seconds'].append(elapsed)
        for d in data.values(): d['median_seconds']=statistics.median(d['seconds'])
        baseline=data['forward_gray']['median_seconds'];candidate=data['centered_half_gray']['median_seconds']
        item=dict(case=name,R=R,beta=beta,precision=ring.precision,
                  f=ring.f,ell=ring.ell,dimension=ring.dimension,
                  methods=data,speedup_vs_gray=baseline/candidate,
                  result_hash=__import__('hashlib').sha256(repr(expected).encode()).hexdigest())
        results.append(item)
        print(json.dumps({'case':name,'gray_s':baseline,'half_s':candidate,'speedup':baseline/candidate}),flush=True,file=sys.stderr)
    return dict(status='PASS',scope='synthetic exact packet coefficient microbenchmark, not SAT runtime',
                environment=dict(python=sys.version,platform=platform.platform(),machine=platform.machine(),
                                 processor=platform.processor(),timer='time.perf_counter',
                                 cpu_info=next((line.strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')),'')),
                seed=202610270209,repeats=3,warmups=1,input_generation_timed=False,
                setup_lifting_and_output_timed=True,results=results)

if __name__=='__main__': print(json.dumps(main(),indent=2,sort_keys=True))
