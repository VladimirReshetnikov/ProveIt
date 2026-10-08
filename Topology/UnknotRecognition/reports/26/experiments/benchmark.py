"""Paired exact determinant-kernel benchmark, NOT an end-to-end knot benchmark."""
import json
import platform
import random
import statistics
import time
from pathlib import Path
from detshadow.linalg import signed_laplacian, TerminalKernel, quotient_cofactor, bareiss
ROOT=Path(__file__).resolve().parents[1]


def case_data(n,b,singular,seed):
    rng=random.Random(seed); ni=n-b
    stop=ni-1 if singular else ni
    edges=[]
    # A connected sparse signed bulk. The final interior vertex of the singular
    # family has total incident weight zero and no interior neighbours.
    for i in range(stop):
        edges.append((i,(i+1)%stop,1))
        edges.append((i,ni+(i%b),1))
        if i+3<stop: edges.append((i,i+3,rng.choice((-1,1,1))))
    for i in range(b-1): edges.append((ni+i,ni+i+1,1))
    if singular: edges.extend([(ni-1,ni,1),(ni-1,ni+1,-1)])
    terminals=list(range(ni,n)); lap=signed_laplacian(n,edges)
    partitions=[]
    for _ in range(96):
        labels=list(range(b))
        for j in range(1,b):
            if rng.random()<0.3: labels[j]=labels[rng.randrange(j)]
        partitions.append(labels)
    return lap,terminals,partitions,edges


def run():
    records=[]
    for ci,(n,b,singular) in enumerate([(32,6,False),(56,6,False),(80,6,False),(56,6,True)]):
        lap,terminals,partitions,edges=case_data(n,b,singular,20261007+ci)
        expected=None; rounds=[]
        for repeat in range(3):
            modes=['directA','directB','compressed']; random.Random(700+ci*10+repeat).shuffle(modes)
            row={'order':modes}
            for mode in modes:
                start=time.perf_counter()
                if mode=='compressed':
                    kernel=TerminalKernel.build(lap,terminals)
                    middle=time.perf_counter()
                    answers=[kernel.query(p) for p in partitions]
                    end=time.perf_counter()
                    row.update(preprocessing_seconds=middle-start,query_seconds=end-middle,
                               nullity=kernel.nullity,
                               max_query_dimension=max((len(kernel.reduced_matrix(p) or []) for p in partitions)))
                else:
                    answers=[bareiss(quotient_cofactor(lap,terminals,p)) for p in partitions]
                    end=time.perf_counter()
                row[mode+'_seconds']=end-start
                if expected is None: expected=answers
                assert answers==expected
            row['paired_speedup']=row['directA_seconds']/row['compressed_seconds']
            row['aa_ratio']=row['directA_seconds']/row['directB_seconds']
            rounds.append(row)
        record=dict(vertices=n,terminals=terminals,singular_family=singular,queries=len(partitions),
                    edges=edges,partitions=partitions,answers=expected,rounds=rounds,
                    median_paired_speedup=statistics.median(x['paired_speedup'] for x in rounds),
                    median_aa_ratio=statistics.median(x['aa_ratio'] for x in rounds),
                    median_direct_seconds=statistics.median(x['directA_seconds'] for x in rounds),
                    median_compressed_seconds=statistics.median(x['compressed_seconds'] for x in rounds))
        records.append(record)
        print(n,'singular',singular,'speedup',round(record['median_paired_speedup'],3),flush=True)
    result=dict(status='passed',scope='exact weighted-graph determinant kernel; not knot recognition',
                python=platform.python_version(),platform=platform.platform(),
                timed='construction of every query matrix; compressed arm includes preprocessing; independent verification excluded',
                records=records)
    (ROOT/'results'/'benchmark.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__': run()
