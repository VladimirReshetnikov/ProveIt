"""Independent finite-completion checks and same-operation timings."""
import argparse, itertools, json, platform, random, statistics, time
from fractions import Fraction as F
from incremental import balance, require


def verify():
    rng = random.Random(20261027)
    fixtures = [[], [[]], [[0,0]], [[5,0],[0,5]], [[2,1],[1,2]]]
    fixtures += [[[rng.randrange(4) if rng.random()<.35 else 0
                   for _ in range(c)] for _ in range(r)]
                  for r in range(1,6) for c in range(1,7)]
    count=completion_count=0
    for A in fixtures:
        for Q in (1,2,3,5):
            results = [balance(A,Q,engine=e,trace=True)
                       for e in ('reference','cached','incremental')]
            signature = lambda x: tuple(x[k] for k in ('rows','columns','loads','initial','final','scores'))
            require(all(signature(x)==signature(results[0]) for x in results), 'identical exact decisions and scores')
            count += 1
            nv=len(A[0]) if A else 0
            if Q<=3 and nv<=3:
                r=results[0]
                C=max([sum(row[j] for row in A) for j in range(nv)]+[1])
                z=F(8*C+1,8*C)
                def potential(labels):
                    cells=[[0]*Q for _ in range(Q)]
                    for a,row in zip(r['rows'],A):
                        for j,w in enumerate(row): cells[a][labels[j]] += w
                    return sum(z**x for row in cells for x in row)
                for j,scores in enumerate(r['scores']):
                    for b,score in enumerate(scores):
                        values=[potential(r['columns'][:j]+[b]+list(tail))
                                for tail in itertools.product(range(Q), repeat=nv-j-1)]
                        require(sum(values)/len(values)==score,'independent completions')
                        completion_count += len(values)
    invalid = [([[1,-1]],2), ([[1],[2,3]],2), ([[True]],2), ([[1]],0)]
    for A,Q in invalid:
        try: balance(A,Q)
        except ValueError: pass
        else: raise RuntimeError('invalid input accepted')
    return dict(fixtures=count, exhaustive_completions=completion_count, rejected_inputs=len(invalid), status='pass')


def bench():
    rng=random.Random(913)
    rows=[]
    for Q,nv,degree in [(8,32,2),(16,48,2),(24,64,2),(24,64,8),(12,32,24)]:
        nr=2*Q
        A=[[0]*nv for _ in range(nr)]
        for j in range(nv):
            for _ in range(degree): A[rng.randrange(nr)][j]+=1
        times={}; outputs={}
        # Alternated order avoids consistently favoring one warm-up position.
        for repetition in range(3):
            for e in (('cached','incremental') if repetition%2==0 else ('incremental','cached')):
                start=time.perf_counter(); out=balance(A,Q,engine=e)
                times.setdefault(e,[]).append(time.perf_counter()-start); outputs[e]=out
        require(outputs['cached']['columns']==outputs['incremental']['columns'],'benchmark labels')
        require(outputs['cached']['final']==outputs['incremental']['final'],'benchmark potential')
        med={e:statistics.median(t) for e,t in times.items()}
        rows.append(dict(labels=Q,columns=nv,rows=nr,column_degree=degree,
                         active_pairs=outputs['cached']['active_pairs'], seconds=times,
                         median_seconds=med,speedup=med['cached']/med['incremental'],
                         operations={e:o['operations'] for e,o in outputs.items()}))
    return dict(python=platform.python_version(),platform=platform.platform(),
                clock='perf_counter',repeats=3, includes='all setup and checks, excludes trace generation',
                scope='component measurements only; not SAT benchmarks or guaranteed speedups',cases=rows)


if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--benchmark',action='store_true'); args=ap.parse_args()
    print(json.dumps(bench() if args.benchmark else verify(),indent=2))
