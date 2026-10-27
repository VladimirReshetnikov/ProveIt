"""End-to-end component timings, common setup/output included; not SAT timings."""
from pathlib import Path
import sys,json,time,statistics,platform,random,gc
from sparse_balancing import balance

def main(target,repetitions=5):
    records=[];rng=random.Random(27102026)
    fixtures=[]
    for Q in (4,8,16,24):
        for density in (.12,.65):
            adj=[[rng.randrange(1,3) if rng.random()<density else 0 for j in range(12)] for i in range(10)]
            fixtures.append((Q,density,adj,'fixed-shape'))
    # Additional fixtures have more vertices than labels on both sides.
    for Q in (8,16,24):
        adj=[[0]*(2*Q) for _ in range(2*Q)]
        for row in adj:
            for j in rng.sample(range(2*Q),4):row[j]=1
        fixtures.append((Q,4/(2*Q),adj,'four-regular-rows'))
    for Q,density,adj,family in fixtures:
        times={m:[] for m in ('cubic','dense','sparse')};cpu={m:[] for m in times};reference=None;stats={}
        # Checked equivalence and symmetric warmup are outside the timed region.
        for method in times:
            out=balance(adj,Q,8,method,certificate=False,checks=True)
            stats[method]=out['stats']
            signature={k:out[k] for k in ('row_labels','column_labels','loads','initial','final')}
            if reference is None:reference=signature
            elif signature!=reference:raise ArithmeticError('warmup output mismatch')
        for rep in range(repetitions):
            # Rotate order to avoid always timing an implementation first.
            order=['cubic','dense','sparse'];order=order[rep%3:]+order[:rep%3]
            for method in order:
                gc.collect();start=time.perf_counter();startcpu=time.process_time()
                out=balance(adj,Q,8,method,certificate=False,checks=False,count=False)
                elapsedcpu=time.process_time()-startcpu
                elapsed=time.perf_counter()-start;times[method].append(elapsed);cpu[method].append(elapsedcpu)
                signature={k:out[k] for k in ('row_labels','column_labels','loads','initial','final')}
                if reference is None:reference=signature
                elif signature!=reference:raise ArithmeticError('benchmark output mismatch')
        med={m:statistics.median(ts) for m,ts in times.items()}
        record=dict(labels=Q,family=family,input_density=density,adjacency=adj,seconds=times,cpu_seconds=cpu,
                    cpu_medians={m:statistics.median(ts) for m,ts in cpu.items()},medians=med,stats=stats,
                    cubic_over_sparse=med['cubic']/med['sparse'],dense_over_sparse=med['dense']/med['sparse'])
        records.append(record);print(Q,density,med,flush=True)
    data=dict(python=sys.version,platform=platform.platform(),repetitions=repetitions,
              timing='Wall and process CPU times; median; rotated order; one checked warmup each; full shared initialization and dense output included; optional invariants and counters disabled equally during timing; operation counts collected in warmup; output equality checked outside timing.',
              comparator='Authored mathematical reference for incoming asymmetric score formula, with shared heap and sparse preprocessing; no incoming code executed.',
              limits='Small component fixtures only. No complete SAT, memory benchmark or universal runtime ratio.',records=records)
    Path(target).write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 5)
