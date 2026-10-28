"""Same-ring matched synthetic component timings; no archive programs executed."""
import argparse
import hashlib
import json
import platform
import random
import statistics
import time
from pathlib import Path
from mixed_projective import Ring,root15,projective,centered,adaptive,direct


def run(repetitions):
    implementation=Path(__file__).with_name('mixed_projective.py')
    source_hash=hashlib.sha256(implementation.read_bytes()).hexdigest()
    benchmark_hash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    rng=random.Random(271028)
    cases=[((2,2,4,4),32,1),((2,2,2,4,4),64,1),
           ((2,2,2,2,4,4),128,1),((2,2,4,4,4),32,1),
           ((2,2,4,4),32,2),((1,1,1,1,1,1,1,1),32,1),
           ((4,4,4),32,1),((2,2,4,4),1,1)]
    records=[]
    for case_index,(beta,p,ell) in enumerate(cases):
        ring=Ring(p,ell);root=root15(ring)
        rows=[[tuple(rng.randrange(-8,9) for _ in range(4*ell)) for _ in beta]
              for _ in range(sum(beta))]
        methods={
            'common_root':lambda stats:projective(rows,beta,ring,root,False,stats),
            'mixed_root':lambda stats:projective(rows,beta,ring,root,True,stats),
            'anisotropic_gray':lambda stats:centered(rows,beta,ring,stats),
            'mixed_fresh_lift':lambda stats:projective(rows,beta,ring,root15(ring),True,stats),
            'common_fresh_lift':lambda stats:projective(rows,beta,ring,root15(ring),False,stats),
            'adaptive':lambda stats:adaptive(rows,beta,ring,root,stats)}
        expected=direct(rows,beta,ring)
        points={};samples={name:[] for name in methods}
        for name,fn in methods.items():
            stats={}; got=fn(stats)
            if got!=expected: raise ArithmeticError('warmup equality')
            points[name]=stats
        names=list(methods)
        for rep in range(repetitions):
            order=names[rep%len(names):]+names[:rep%len(names)]
            if rep&1: order=order[::-1]
            for name in order:
                stats={};cpu=time.process_time();wall=time.perf_counter()
                got=methods[name](stats)
                elapsed=time.perf_counter()-wall;cpu_elapsed=time.process_time()-cpu
                if got!=expected: raise ArithmeticError('timed equality')
                samples[name].append(dict(wall_seconds=elapsed,cpu_seconds=cpu_elapsed))
        medians={name:{kind:statistics.median(x[kind] for x in xs)
                       for kind in ('wall_seconds','cpu_seconds')}
                 for name,xs in samples.items()}
        records.append(dict(beta=beta,precision=p,ell=ell,ring_dimension=4*ell,
                            stats=points,samples=samples,medians=medians,
                            common_to_mixed=medians['common_root']['wall_seconds']/medians['mixed_root']['wall_seconds'],
                            gray_to_mixed=medians['anisotropic_gray']['wall_seconds']/medians['mixed_root']['wall_seconds'],
                            fresh_common_to_fresh_mixed=medians['common_fresh_lift']['wall_seconds']/medians['mixed_fresh_lift']['wall_seconds'],
                            gray_to_fresh_mixed=medians['anisotropic_gray']['wall_seconds']/medians['mixed_fresh_lift']['wall_seconds']))
        print(json.dumps(dict(case=case_index,beta=beta,common_to_mixed=records[-1]['common_to_mixed'],
                              gray_to_mixed=records[-1]['gray_to_mixed'])),flush=True)
    if hashlib.sha256(implementation.read_bytes()).hexdigest()!=source_hash:
        raise ArithmeticError('implementation changed during benchmark')
    return dict(scope='Synthetic exact packet component, not SAT runtime. Polynomial ring rank is identical within every comparison.',
                implementation_sha256=source_hash,benchmark_script_sha256=benchmark_hash,
                python=platform.python_version(),platform=platform.platform(),
                repetitions=repetitions,seed=271028,
                policy='One common warmup per method; rotated/reversed timed order; canonicalization, root validation, increments, extraction and output included. Root cached except both fresh-lift variants, which charge classical precision-doubling root construction. Input generation and independent oracle excluded.',
                cases=records)


if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--repetitions',type=int,default=3)
    ap.add_argument('--output',required=True);args=ap.parse_args()
    Path(args.output).write_text(json.dumps(run(args.repetitions),indent=2)+'\n')
