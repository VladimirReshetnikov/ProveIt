"""Actual universal finite-support CA steps, no source-boundary shortcut."""
import json
import random
import resource
import time
from hashlib import sha256
from pathlib import Path
import lazy_reversible as lazy

HERE=Path(__file__).resolve().parent
SOURCE=HERE/'source.json'
SOURCE_SHA='fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3'

def check(value, detail):
    if not value: raise RuntimeError(detail)

def main():
    begin=time.perf_counter()
    raw=SOURCE.read_bytes()
    check(sha256(raw).hexdigest()==SOURCE_SHA,'Universal source hash mismatch')
    data=json.loads(raw)
    del raw
    start=time.perf_counter()
    a=lazy.compile_lazy_source(data)
    compile_seconds=time.perf_counter()-start
    del data
    check((a.m,a.p,a.a,a.J,a.factors)==(122622,66066,75495,0,269291358255),'Universal ledger mismatch')
    x=a.encode('START',1,0)
    check(sorted(x)==[-20380381,0,1019018,1019019,20380380],'Published loader mismatch')
    trail=[]
    begin_steps=time.perf_counter()
    for step in range(128):
        y,stats=a.step(x,verify=True,trace=True)
        check(a.step(y,inverse=True,verify=True)==x,('Universal startup inverse failed',step))
        check(len(y)==5,'Universal mass changed')
        if step<3:
            target=('h0000B0T1','p00001R0T1','p00001R0T2')[step]
            check(y==a.encode(target,1,0),('Universal direct startup mismatch',step))
        trail.append(dict(step=step,input=sorted(x),output=sorted(y),stats=dict(stats)))
        x=y
    step_seconds=time.perf_counter()-begin_steps
    # Start elsewhere in the huge index space, on arbitrary endpoint+noise
    # configurations. These are genuine global evaluations, without promised
    # source-ID decoding. Round trips are not a substitute for eager comparison;
    # the latter is separately done on thousands of small-source configurations.
    rng=random.Random(202610030541)
    malformed=[]
    begin_malformed=time.perf_counter()
    for trial in range(128):
        index=rng.randrange(a.factors)
        g=a.gate_at(index)
        sign=rng.randrange(2)
        shift=-(1<<512) if trial==0 else rng.randrange(-100000000,100000001)
        x=frozenset(shift+v for v in g.shapes[sign])
        for _ in range(rng.randrange(4)):
            x=x|{shift+rng.randrange(-2*a.Z,2*a.Z+1)}
        y,stats=a.step(x,inverse=bool(trial%2),verify=True,trace=True)
        check(a.step(y,inverse=not bool(trial%2),verify=True)==x,('Malformed universal inverse failed',trial))
        check(len(y)==len(x),'Malformed universal mass changed')
        malformed.append(dict(trial=trial,seed_factor=index,input=sorted(x),output=sorted(y),stats=dict(stats)))
    receipt=dict(status='passed',ledger=a.ledger(),source_sha256=SOURCE_SHA,
                 compiler_sha256=lazy.FROZEN_SHA256,
                 evaluator_sha256=sha256((HERE/'lazy_reversible.py').read_bytes()).hexdigest(),
                 compilation_seconds=compile_seconds,startup_steps=128,startup_seconds=step_seconds,
                 malformed_cases=128,malformed_seconds=time.perf_counter()-begin_malformed,
                 total_seconds=time.perf_counter()-begin,
                 peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                 maximum_startup_tested_factors=max(s['stats']['tested_factors'] for s in trail),
                 maximum_startup_changed_factors=max(s['stats']['changed_factors'] for s in trail),
                 maximum_malformed_tested_factors=max(s['stats']['tested_factors'] for s in malformed),
                 maximum_malformed_changed_factors=max(s['stats']['changed_factors'] for s in malformed))
    (HERE/'universal-startup-trace.json').write_text(json.dumps(trail,indent=2)+'\n')
    (HERE/'universal-malformed-trace.json').write_text(json.dumps(malformed,indent=2)+'\n')
    suffix='' if __debug__ else '-optimized'
    (HERE/f'universal{suffix}-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
