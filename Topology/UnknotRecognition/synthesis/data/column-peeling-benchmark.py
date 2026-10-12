"""Paired isolated-kernel and full supplied-cut comparisons, with A/A controls.

Run after validation on an otherwise idle host. Source geometry is excluded
only from explicitly labelled prepared-core measurements. No result measures
full unknot recognition or discovery. Baseline modules are retained verbatim.
"""
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys
import time
ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).parent
sys.path[:0] = [str(ROOT/'fast'), str(HERE/'column-baseline')]
from loader import load
from fastunknot.core_handlebody import column_cancellation_plan, core_handlebody_certificate
from fastunknot.column_cancellation_verify import verify_column_cancellations
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.integer_codec import json_safe
from normal_orbit_research.seeds import sources


def main():
    old = load()
    pins = sources()
    bank_path = ROOT/'fast/marked_parallelity_research/corpus.json'
    bank = json.loads(bank_path.read_text())['cases']
    rng = random.Random(951297)
    report = dict(native_source_sha256=pins, python=sys.version, platform=platform.platform(),
                  seed=951297, rounds=5, cases=[],
                  driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  corpus_sha256=hashlib.sha256(bank_path.read_bytes()).hexdigest(),
                  baseline_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in sorted((HERE/'column-baseline').glob('*.py'))})
    output = Path(__file__).with_suffix('.json')
    def paired(label, before, after, **meta):
        def timed(fn):
            start = time.perf_counter()
            fn()
            return time.perf_counter()-start
        before(); after()
        samples=[]
        for _ in range(5):
            order=['old','new']; rng.shuffle(order); sample=dict(order=order)
            for name in order:
                sample[name]=timed(before if name=='old' else after)
            samples.append(sample)
        aa=[]
        for _ in range(3):
            first, second=timed(before),timed(before)
            aa.append(dict(first=first,second=second,ratio=first/second))
        record=dict(label=label, **meta, samples=samples, aa_samples=aa,
                    old_median=statistics.median(s['old'] for s in samples),
                    new_median=statistics.median(s['new'] for s in samples),
                    paired_speedup=statistics.median(s['old']/s['new'] for s in samples),
                    aa_median=statistics.median(s['ratio'] for s in aa))
        report['cases'].append(record)
        output.write_text(json.dumps(json_safe(report),indent=2)+'\n')
        print(json.dumps({k:v for k,v in record.items() if k not in ('samples','aa_samples')}),flush=True)
    for size in (128,512,2048):
        counts={r:{r:1,r+1:1} for r in range(size)}
        baseline=old['core_handlebody'].capped_cancellation_plan(counts)
        current=column_cancellation_plan(counts)
        assert not baseline['remaining_rows'] and not current['remaining_rows']
        assert verify_column_cancellations(counts,baseline['cancellations'])
        assert verify_column_cancellations(counts,current['cancellations'])
        paired(f'matrix-chain-{size}',
               lambda: old['core_handlebody'].capped_cancellation_plan(counts),
               lambda: column_cancellation_plan(counts),
               scope='isolated cancellation production',rows=size,incidences=2*size,
               old_work=baseline['stats'],new_work=current['stats'])
    for size in (64,128,256):
        core=dict(handles0=[dict(id=0)],
                  handles1=[dict(id=i,ends=[0,0]) for i in range(size+1)],
                  handles2=[dict(id=i,cycle=[dict(dimension=0,handle=0),dict(dimension=1,handle=i),
                                            dict(dimension=0,handle=0),dict(dimension=1,handle=i+1)])
                            for i in range(size)],handles3=[])
        a=old['core_handlebody'].core_handlebody_certificate(core)
        b=core_handlebody_certificate(core)
        assert a['status']==b['status']=='COMPLETE'
        def replay(fn,cert):
            assert fn(core,cert)
        paired(f'conditional-replay-chain-{size}',
               lambda: replay(old['core_handlebody_verify'].verify_core_handlebody_certificate,a['certificate']),
               lambda: replay(verify_core_handlebody_certificate,b['certificate']),
               scope='conditional geometric-chart replay; not a source knot',rows=size)
    cores=[]
    for case in bank:
        prepared=_prepare(case['triangulation'],lambda:None)
        vector=_coordinates(prepared,case['coordinates'],lambda:None)
        cores.append(_parallelity_geometry(prepared,vector,lambda:None)['core'])
    def cohort(fn):
        return [fn(core) for core in cores]
    previous=cohort(old['core_handlebody'].core_handlebody_certificate)
    current=cohort(core_handlebody_certificate)
    assert [r['status'] for r in previous]==[r['status'] for r in current]
    paired('prepared-106-core-production',lambda:cohort(old['core_handlebody'].core_handlebody_certificate),
           lambda:cohort(core_handlebody_certificate),scope='prepared source cores; geometry excluded',
           complete=sum(r['status']=='COMPLETE' for r in current))
    def core_replays(fn,results):
        for core,result in zip(cores,results):
            if result['status']=='COMPLETE': assert fn(core,result['certificate'])
    paired('prepared-common-core-replay',
           lambda:core_replays(old['core_handlebody_verify'].verify_core_handlebody_certificate,previous),
           lambda:core_replays(verify_core_handlebody_certificate,current),scope='prepared source cores; geometry excluded')
    compatibility=json.loads((HERE/'column-peeling-compatibility.json').read_text())['cases']
    refused=[r['id'] for r in compatibility if r['precheck_skipped_boundary']]
    byid={c['id']:c for c in bank}
    chosen=['pilot/lst_4_7/0','fibonacci_lst_09/mixed',
            'pilot/fibonacci_lst_07/0','pilot/fibonacci_lst_09/0']
    # Choose the smallest and largest prechecked source, without timing selection.
    refused.sort(key=lambda key:(len(byid[key]['triangulation']['tetrahedra']),key))
    chosen.extend([refused[0],refused[-1]])
    def query(c,producer,verifier):
        value=producer(c['triangulation'],c['coordinates'],record_certificate=True)
        if value['status']=='COMPLETE':
            assert verifier(c['triangulation'],c['coordinates'],value['certificate'])
        return value
    for name in chosen:
        c=byid[name]
        before=lambda:query(c,old['normal_cut_handlebodies'].normal_cut_handlebodies,
                            old['normal_cut_handlebodies_verify'].verify_normal_cut_handlebodies)
        after=lambda:query(c,normal_cut_handlebodies,verify_normal_cut_handlebodies)
        a,b=before(),after()
        assert a['status']==b['status']
        if a['status']=='COMPLETE':assert a['census']['histogram']==b['census']['histogram']
        paired(name,before,after,scope='whole supplied-cut query including replay on success',
               status=b['status'],tetrahedra=len(c['triangulation']['tetrahedra']),
               old_schema=a.get('certificate',{}).get('schema'),new_schema=b.get('certificate',{}).get('schema'))
    assert pins==sources(),'source changed during measurements'
    report['finished']=True
    output.write_text(json.dumps(json_safe(report),indent=2)+'\n')


if __name__=='__main__':main()
