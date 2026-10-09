"""Deterministic source-profile audit against explicit disjoint-set components."""
import collections,hashlib,json,platform,random,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'src'))
from orbit_transfer import compile_transfer
from orbit_transfer.reference import make_trace,literal_components

rng=random.Random(261008611);start=time.perf_counter();ops=collections.Counter()
maximum=dict(circuit_nodes=0,source_events=0,peak_runs=0,emissions=0)
for iteration in range(10000):
    n=rng.randrange(1,65);rows=[]
    for _ in range(rng.randrange(13)):
        w=rng.randrange(1,n+1);a,c=rng.randrange(n-w+1),rng.randrange(n-w+1)
        rows.append((a,a+w-1,c,c+w-1,rng.choice((-1,1))))
    cuts=sorted({0,n}|{rng.randrange(n+1) for _ in range(16)})
    proof=make_trace(n,rows,version=1+iteration%2)
    prog=compile_transfer(n,rows,proof,cuts)
    expected=collections.Counter(tuple(sum(a<=x<b for x in orbit)
        for a,b in zip(cuts,cuts[1:])) for orbit in literal_components(n,rows))
    actual=collections.Counter()
    for e in prog.emissions:actual[tuple(prog.circuit.transpose([(e.node,1)]))]+=e.multiplicity
    assert expected==actual,(iteration,n,rows,cuts)
    assert prog.circuit.transpose([(e.node,e.multiplicity) for e in prog.emissions])==[b-a for a,b in zip(cuts,cuts[1:])]
    assert max(prog.circuit.evaluate([1]*(len(cuts)-1)),default=0)<=n
    for key in maximum:maximum[key]=max(maximum[key],prog.stats[key])
    ops.update(e['op'] for e in proof['operations'])
result=dict(status='PASS',cases=10000,classical_traces=5000,sharp_traces=5000,
            seed=261008611,elapsed_seconds=time.perf_counter()-start,
            checks=['every emitted source profile against literal graph',
                    'all source-cell masses conserved', 'all gate masses <= universe size'],
            rule_events=dict(ops),maxima=maximum,python=sys.version,platform=platform.platform(),
            source_sha256={str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest()
                           for f in sorted((ROOT/'src').rglob('*.py'))})
(ROOT/'results'/'audit.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
