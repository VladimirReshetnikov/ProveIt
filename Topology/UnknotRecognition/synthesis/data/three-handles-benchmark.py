"""Complete supplied-cut queries, including independent native proof replay.

Newly supported cases are compared with Regina's explicit cut and component
recognition. Prior native refusals are not timed as if they did equivalent
work. Run after all validation processes finish.
"""
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time
ROOT=Path(__file__).resolve().parents[2];sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from marked_parallelity_research.benchmark_census import native,explicit
from normal_orbit_research.seeds import sources


def main():
    import regina
    pins=sources();rng=random.Random(26101263)
    path=ROOT/'fast/marked_parallelity_research/corpus.json'
    bank={c['id']:c for c in json.loads(path.read_text())['cases']}
    sources_to_try=['pilot/interior_1_2/0','pilot/interior_2_3/0','pilot/interior_3_5/0',
                    'pilot/finite_trefoil_interior/0','interior_1_2/mixed','interior_3_5/mixed',
                    'finite_figureEight_interior/mixed']
    report=dict(native_source_sha256=pins,python=sys.version,platform=platform.platform(),
                regina=regina.versionString(),seed=26101263,rounds=5,cases=[],capacity=[],
                corpus_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    output=Path(__file__).with_suffix('.json')
    for key in sources_to_try:
        c=bank[key];raw=c['triangulation']
        for copies in ((1,64) if key in ('interior_1_2/mixed','finite_figureEight_interior/mixed') else (1,)):
            rows=[[copies*v for v in row] for row in c['coordinates']]
            reference,_=explicit(raw,rows);value,_=native(raw,rows)
            assert value['certificate']['schema']=='normal-cut-handlebodies-v6'
            assert value['census']['histogram']==reference['histogram']
            samples=[]
            for _ in range(5):
                order=['native','explicit'];rng.shuffle(order);sample=dict(order=order)
                for name in order:
                    result,timing=(native if name=='native' else explicit)(raw,rows)
                    if name=='native':assert result['census']['histogram']==reference['histogram']
                    else:assert result['histogram']==reference['histogram']
                    sample[name]=timing
                samples.append(sample)
            aa=[]
            for _ in range(3):
                _,first=explicit(raw,rows);_,second=explicit(raw,rows)
                aa.append(dict(first=first,second=second,ratio=first/second))
            record=dict(source=key,copies=copies,tetrahedra=len(raw['tetrahedra']),
                        histogram=reference['histogram'],explicit_cut_tetrahedra=reference['tetrahedra'],
                        cancelled_23=len(value['certificate']['core_reduction']['cancellations']),
                        native_median=statistics.median(s['native']['total'] for s in samples),
                        explicit_median=statistics.median(s['explicit'] for s in samples),
                        paired_speedup=statistics.median(s['explicit']/s['native']['total'] for s in samples),
                        aa_median=statistics.median(s['ratio'] for s in aa),samples=samples,aa_samples=aa)
            report['cases'].append(record)
            output.write_text(json.dumps(json_safe(report),indent=2)+'\n')
            print(json.dumps({k:v for k,v in record.items() if k not in ('samples','aa_samples')}),flush=True)
    c=bank['interior_1_2/mixed'];rows=[[(1<<16384)*v for v in row] for row in c['coordinates']]
    value,timing=native(c['triangulation'],rows)
    encoded=json.dumps(json_safe(value['certificate']),sort_keys=True).encode()
    started=time.perf_counter()
    assert verify_normal_cut_handlebodies(c['triangulation'],json_safe(rows),json_safe(value['certificate']))
    hex_replay_seconds=time.perf_counter()-started
    report['capacity'].append(dict(source=c['id'],multiplicity_power=16384,timing=timing,hex_replay_seconds=hex_replay_seconds,
        histogram=value['census']['histogram'],certificate_bytes=len(encoded),certificate_sha256=hashlib.sha256(encoded).hexdigest()))
    assert sources()==pins
    report['finished']=True
    output.write_text(json.dumps(json_safe(report),indent=2)+'\n')
    print('Finished nine paired cases and one binary-capacity case.',flush=True)


if __name__=='__main__':main()
