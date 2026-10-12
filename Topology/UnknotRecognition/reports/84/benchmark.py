"""Paired COMPLETE H1-kernel measurements on abstract interface models.

Both arms use the same Smith implementation and its independent replay. The
condensed arm also replays its condensation. No normal-cut extraction, AHT,
Regina, diagram input, or complete knot recognition is timed or claimed.
"""
from __future__ import annotations
from dataclasses import asdict
import gc
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter_ns
from interface_homology import *
from interface_homology.smith import smith, verify_smith, torsion_blocks
from tests.oracle import expand

ROOT=Path(__file__).resolve().parent


def compressed(model):
    p=condense(model)
    if not verify_condensation(model,p):raise AssertionError('condensation replay failed')
    s=smith(p.matrix,cols=p.relation_count)
    if not verify_smith(p.matrix,s,cols=p.relation_count):raise AssertionError('Smith replay failed')
    output={'b0':p.b0,'b1':p.rows-len(s.diagonal)+p.free_bulk,
            'torsion':torsion_blocks(s.diagonal,p.two_torsion_bulk)}
    return json.dumps(wire(output),sort_keys=True,separators=(',',':'))


def expanded(model):
    a,n,b0=expand(model,max_generators=100000)
    s=smith(a,cols=n)
    if not verify_smith(a,s,cols=n):raise AssertionError('expanded Smith replay failed')
    output={'b0':b0,'b1':len(a)-len(s.diagonal),'torsion':torsion_blocks(s.diagonal)}
    return json.dumps(wire(output),sort_keys=True,separators=(',',':'))


def cases():
    core=Core(1,((0,0),))
    for g in [0,1,8,64,512,4096]:
        yield f'saturated_genus_{g}',Model(core,(Surface(True,g,2,circles=(Loop(0,(1,)),Loop(0,(-1,)))),))
    for m in [1,8,32]:
        yield f'closed_nonorientable_copies_{m}',Model(Core(0),(Surface(False,3,0,m),))
    yield 'core_only_tiny',Model(core)
    rng=random.Random(177)
    words=[]
    for _ in range(9):
        word=[]
        for j in range(10):
            coeff=rng.randrange(-2,3)
            word.extend(((j+1) if coeff>0 else -(j+1),)*abs(coeff))
        words.append(Loop(0,tuple(word)))
    yield 'core_only_relations',Model(Core(1,tuple((0,0)for _ in range(10)),tuple(words)))


def main():
    rng=random.Random(2026101211)
    samples=[]; summaries=[]
    for name,model in cases():
        answer=compressed(model)
        if expanded(model)!=answer:raise AssertionError(name)
        p=condense(model); a,n,_=expand(model,max_generators=100000)
        local=[]
        for round_no in range(10): # one warmup, nine retained paired rounds
            arms=['compressed','expanded','compressed_AA'];rng.shuffle(arms)
            times={}
            for arm in arms:
                gc.collect()
                fn=expanded if arm=='expanded' else compressed
                begin=perf_counter_ns();observed=fn(model);elapsed=perf_counter_ns()-begin
                if observed!=answer:raise AssertionError((name,arm))
                row={'case':name,'round':round_no,'warmup':round_no==0,
                     'arm':arm,'nanoseconds':elapsed,'order':arms,
                     'answer_sha256':hashlib.sha256(observed.encode()).hexdigest()}
                samples.append(row);times[arm]=elapsed
            if round_no:local.append(times)
        summaries.append({'case':name,'input_sha256':fingerprint(model),
            'expanded_shape':[len(a),n],'condensed_shape':[p.rows,p.relation_count],
            'compressed_median_ms':statistics.median(x['compressed']for x in local)/1e6,
            'expanded_median_ms':statistics.median(x['expanded']for x in local)/1e6,
            'median_paired_ratio':statistics.median(x['expanded']/x['compressed']for x in local),
            'median_AA_ratio':statistics.median(x['compressed_AA']/x['compressed']for x in local)})
    huge=[]
    for exponent in [64,256,1024,4096,16384]:
        n=1<<exponent
        # Simultaneously large genus and multiplicity, not merely a large
        # integer coefficient in a fixed explicit presentation.
        model=Model(Core(0),(Surface(False,n+1,0,n),))
        timings=[]
        for _ in range(10):
            begin=perf_counter_ns();answer=compressed(model);timings.append(perf_counter_ns()-begin)
        p=condense(model)
        huge.append({'parameter_exponent':exponent,'matrix_shape':[p.rows,p.relation_count],
            'free_rank_formula':'2^(2*exponent)','two_torsion_multiplicity_formula':'2^exponent',
            'output_bytes':len(answer.encode()),'median_ms':statistics.median(timings[1:])/1e6,
            'samples_ns':timings,'expanded_arm':'not run; no timing ratio asserted'})
    data={'scope':__doc__,'python':sys.version,'platform':platform.platform(),
          'rounds':9,'warmups':1,'shuffle_seed':2026101211,
          'summaries':summaries,'samples':samples,'binary_stress':huge,
          'source_hashes':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
              for p in [ROOT/'benchmark.py',ROOT/'tests/oracle.py']+sorted((ROOT/'interface_homology').glob('*.py'))}}
    (ROOT/'results/benchmark.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'summaries':summaries,'binary_stress':huge},indent=2))

if __name__=='__main__':main()
