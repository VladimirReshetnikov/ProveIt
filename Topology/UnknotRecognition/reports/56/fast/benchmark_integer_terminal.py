"""Pinned native-stage comparison of rational, direct and reusable integer observers."""
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
import sys
from time import perf_counter
from types import ModuleType

FAST=Path(__file__).resolve().parent
ROOT=FAST.parent
REPO=ROOT.parents[1]
sys.path[:0]=[str(FAST/'determinant_research'),str(ROOT/'reports/26')]
from boundary_tait import BoundaryTait
from fastunknot import Diagram
from fastunknot.scan_fast import FastScan
from detshadow.linalg import bareiss,quotient_cofactor
from benchmark_boundary import WORD,ORDER

BASELINE='7951ae852b743fa0d865bc323d6b8c82441c5582'


def main():
    path='Topology/UnknotRecognition/fast/determinant_research/boundary_tait.py'
    source=subprocess.check_output(['git','show',BASELINE+':'+path],cwd=REPO)
    old=ModuleType('pinned_boundary');old.__file__=str(FAST/'determinant_research/boundary_tait.py')
    exec(compile(source,BASELINE+':'+path,'exec'),old.__dict__)
    records_path=ROOT/'synthesis/data/dynamic-terminal-native-queries.json'
    records=json.loads(records_path.read_text())
    cases={'native_all':records}
    details={}
    for extra in (4,16,32):
        # Two adjacent generator pairs grow both face shadings, unlike the
        # older single-generator padding whose selected graph stays at v=9.
        d=Diagram.from_braid(5,WORD+[1,2,-2,-1]*extra)
        order=ORDER+list(range(len(WORD),d.crossings));scan=FastScan(shape_cache=False)
        for index in order[:9]:scan.add_crossing(d.pd[index])
        pairs=[scan.algebra.pairs[m] for m in sorted(set(scan.mid)-{None})]
        geometry=BoundaryTait(d.pd,order,9)
        connected=[p for p in pairs if geometry.partition(p)['shadow_components']==1]
        for scope,queries in [('one',connected[:1]),('all',pairs)]:
            name=f'padding_{extra}_{scope}'
            cases[name]=[dict(pd=d.pd,order=order,stage=9,matchings=queries)]
            details[name]=dict(crossings=d.crossings,vertices=len(geometry.laplacian),
                               terminals=len(geometry.terminals),queries=len(queries))
    cases['padding_32_repeated']=[dict(cases['padding_32_one'][0],
                                     matchings=cases['padding_32_one'][0]['matchings']*200)]
    details['padding_32_repeated']=dict(details['padding_32_one'],queries=200)
    paths=[Path(__file__),FAST/'benchmark_boundary.py',records_path,
           FAST/'determinant_research/boundary_tait.py',FAST/'fastunknot/terminal_determinant.py',
           FAST/'fastunknot/integer_determinant.py',FAST/'fastunknot/diagram.py',
           FAST/'fastunknot/boundary_connectivity.py',FAST/'fastunknot/scan_fast.py',
           ROOT/'reports/26/detshadow/linalg.py',ROOT/'reports/26/detshadow/diagram.py']
    hashes={str(p.relative_to(REPO)):sha256(p.read_bytes()).hexdigest() for p in paths}

    def run(rows,arm):
        out=[];stats=dict(kernel_setups=0,direct_queries=0,cache_entries=0)
        for row in rows:
            d=Diagram.from_pd(row['pd'])
            cls=old.BoundaryTait if arm in ('rational','control') else BoundaryTait
            kwargs={} if arm in ('rational','control') else dict(arithmetic='integer')
            g=cls(d.pd,row['order'],row['stage'],**kwargs)
            values=[]
            for pairs in row['matchings']:
                if arm in ('rational','control','integer_kernel'):
                    values.append(g.evaluate(pairs));continue
                meta=g.partition(pairs)
                if meta['shadow_components']!=1:
                    values.append(((0,0),meta));continue
                names={};key=tuple(names.setdefault(v,len(names)) for v in meta['partition'])
                if key not in g.cache:
                    if arm=='direct' or len(g.cache)<4:
                        g.cache[key]=bareiss(quotient_cofactor(g.laplacian,g.terminals,key))
                        stats['direct_queries']+=1
                    else:
                        g.prepare_kernel();g.cache[key]=g.kernel.query(key)
                unit=((1,0),(0,-1),(-1,0),(0,1))[meta['phase']]
                v=g.cache[key];values.append(((unit[0]*v,unit[1]*v),meta))
            stats['kernel_setups']+=int(g.kernel is not None)
            stats['cache_entries']+=len(g.cache)
            out.append(values)
        return out,stats

    arms=('rational','control','direct','integer_kernel','adaptive_four')
    rng=random.Random(261008119);samples=[];expected={}
    # Fixed batches keep small observations above a few milliseconds without
    # calibrating the batch count from a favoured implementation.
    repeats={name:(10 if name=='padding_4_one' else 1) for name in cases}
    for round_number in range(6):
        jobs=[(name,arm) for name in cases for arm in arms];rng.shuffle(jobs)
        for name,arm in jobs:
            start=perf_counter();results=[run(cases[name],arm) for _ in range(repeats[name])]
            elapsed=(perf_counter()-start)/repeats[name]
            digests={sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
                     for value,_ in results}
            assert len(digests)==1;digest=digests.pop()
            if name in expected:assert expected[name]==digest,(name,arm)
            expected[name]=digest
            samples.append(dict(case=name,arm=arm,round=round_number,warmup=round_number==0,
                                seconds=elapsed,result_sha256=digest,stats=results[-1][1]))
        print('completed round',round_number,flush=True)
    for p in paths:assert sha256(p.read_bytes()).hexdigest()==hashes[str(p.relative_to(REPO))]
    summary={}
    for name in cases:
        summary[name]={}
        for arm in arms:
            rows=[r for r in samples if r['case']==name and r['arm']==arm and not r['warmup']]
            ratios=[next(r['seconds'] for r in samples if r['case']==name and r['arm']=='rational'
                         and r['round']==s['round'])/s['seconds'] for s in rows]
            summary[name][arm]=dict(median_seconds=statistics.median(r['seconds'] for r in rows),
                paired_rational_ratio=statistics.median(ratios),stats=rows[0]['stats'])
    out=dict(scope=__doc__,baseline=BASELINE,baseline_source_sha256=sha256(source).hexdigest(),
             source_sha256=hashes,seed=261008119,python=platform.python_version(),measured=200,warmups=40,
             repetitions=repeats,details=details,summary=summary,samples=samples,
             timing='Fresh native PD, geometry, algebra setup, all queries and cache activity included. '
                    'Archive loading, workload construction, hashing and independent verification excluded. '
                    'Rational and identical control use the pinned old source. Direct and adaptive-four '
                    'are experimental policies; adaptive starts with four distinct integer quotient queries. '
                    'All arms use the same normalized partition cache. This is not full-recognizer timing.')
    (FAST/'results/integer_terminal_20261008.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
