#!/usr/bin/env python3
"""Paired timings; not a comparison with the full fastunknot pipeline."""
import csv
import json
import platform
import random
import statistics
import time
from pathlib import Path
from ranktwo import compress, optimal_pass, verify
from ranktwo.families import sleeved_unknot, shortening_barrier, survivor_lower_bound
from ranktwo.oracles import brute_optimum


def timed(call):
    t=time.perf_counter();answer=call();return time.perf_counter()-t,answer


def main():
    rng=random.Random(81007); rows=[]; repeats=3
    # Warm up both implementations without timing compilation/import overhead.
    optimal_pass(3,(1,2,-1,-2)*4);brute_optimum(3,(1,2,-1,-2)*4)
    for n in (16,32,64,128):
        word=tuple(rng.choice((1,-1,2,-2)) for _ in range(n))
        values={'avl':[],'brute':[]};saved=None
        for rep in range(repeats):
            order=['avl','brute'];rng.shuffle(order)
            for method in order:
                if method=='avl':
                    elapsed,result=timed(lambda:optimal_pass(3,word))
                    score=n-len(result[0])
                else:
                    elapsed,score=timed(lambda:brute_optimum(3,word))
                assert saved is None or saved==score
                saved=score;values[method].append(elapsed)
        rows.append({'family':'paired-random-B3','parameter':n,'strands':3,'input_letters':n,
                     'output_letters':n-saved,'repeats':repeats,
                     'avl_seconds':statistics.median(values['avl']),
                     'brute_seconds':statistics.median(values['brute']),
                     'speed_ratio':statistics.median(values['brute'])/statistics.median(values['avl']),
                     'samples':values})
    for family,parameters in [('sleeved-unknot',(16,64,256,1024,4096)),
                              ('shortening-barrier',(8,32,128,512,2048))]:
        for p in parameters:
            word=sleeved_unknot(4,p) if family=='sleeved-unknot' else shortening_barrier(p)
            values=[]; verification=[];hash_values=[]
            for _ in range(repeats):
                elapsed,result=timed(lambda:compress(4,word,max_passes=1,dictionary='avl'))
                verify_elapsed,replayed=timed(lambda:verify(4,word,result['certificate']))
                hash_elapsed,other=timed(lambda:compress(4,word,max_passes=1,dictionary='hash'))
                assert result['certificate']==other['certificate']
                assert replayed[0]==tuple(result['word'])
                values.append(elapsed);verification.append(verify_elapsed);hash_values.append(hash_elapsed)
            statistics_pass=result['stats']['passes'][0]
            row={'family':family,'parameter':p,'strands':4,'input_letters':len(word),
                 'output_letters':len(result['word']),'repeats':repeats,
                 'avl_seconds':statistics.median(values),'hash_seconds':statistics.median(hash_values),
                 'verify_seconds':statistics.median(verification),
                 'certificate_steps':len(result['certificate']['steps']),
                 'removed_nodes':replayed[1]['removed_nodes'],
                 'state_queries':statistics_pass['state_queries'],
                 'quotient_nodes':statistics_pass['quotient_nodes'],
                 'group_advances':statistics_pass['group_advances'],
                 'samples':{'avl':values,'hash':hash_values,'verify':verification}}
            rows.append(row)
    lower_bounds=[]
    for m in (1,2,4,5,8,16,32,64):
        lower_bounds.append({'m':m,'prefix_crossings':2*m,'survivor_lower_bound':str(survivor_lower_bound(m))})
    result={'python':platform.python_version(),'platform':platform.platform(),
            'processor':platform.processor(),'seed':81007,'timer':'time.perf_counter',
            'repeats':repeats,'note':'Paired random-word baseline is our slow interval oracle, not fastunknot.',
            'benchmarks':rows,'exact_lower_bounds':lower_bounds}
    destination=Path('results');destination.mkdir(exist_ok=True)
    (destination/'benchmarks.json').write_text(json.dumps(result,indent=2)+'\n')
    fields=['family','parameter','strands','input_letters','output_letters','avl_seconds',
            'hash_seconds','verify_seconds','brute_seconds','speed_ratio','certificate_steps',
            'group_advances','state_queries','quotient_nodes','removed_nodes']
    with (destination/'benchmarks.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore');writer.writeheader();writer.writerows(rows)
    for row in rows:
        print(row['family'],row['input_letters'],'->',row['output_letters'],
              'AVL',round(row['avl_seconds'],6),'s',
              'ratio',round(row.get('speed_ratio',0),1))
    print('Exact matching-summand lower bounds:',lower_bounds)

if __name__=='__main__':main()
