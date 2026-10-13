"""Paired complete-query latency; new-case inconclusive and complete are distinct tasks.

Diagnostic follow-up to the initial Fibonacci-8 regression; do not pool runs.
Run with no concurrent validation. Twenty-one AB/BA pairs plus seven baseline A/A
controls, warm workers, time production and positive independent replay.
Startup, case loading, certificate hashing and JSON output are outside timing.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time
ROOT=Path(__file__).resolve().parents[2]
DATA=Path(__file__).parent
IDS=['pilot/fibonacci_lst_08/0']


def worker(fast):
    sys.path.insert(0,str(fast))
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    from fastunknot.integer_codec import json_safe
    cases={c['id']:c for n in ('corpus.json','three_handle_corpus.json')
           for c in json.loads((ROOT/'fast/marked_parallelity_research'/n).read_text())['cases']}
    cases.update((c['id'],c) for c in json.loads((ROOT/'fast/signed_annulus_research/corpus.json').read_text())['cases'])
    for line in sys.stdin:
        q=json.loads(line); c=cases[q['id']]
        start=time.perf_counter()
        r=normal_cut_handlebodies(c['triangulation'],c['coordinates'],record_certificate=True)
        produced=time.perf_counter()
        if r['status']=='COMPLETE':
            assert verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],r['certificate'])
        end=time.perf_counter()
        proof=json.dumps(json_safe(r.get('certificate')),sort_keys=True,separators=(',',':')).encode()
        print(json.dumps(dict(status=r['status'],produce=produced-start,replay=end-produced,
                              total=end-start,certificate_sha256=hashlib.sha256(proof).hexdigest())),flush=True)


def main():
    p=argparse.ArgumentParser();p.add_argument('--worker',type=Path);p.add_argument('--baseline',type=Path)
    a=p.parse_args()
    if a.worker:return worker(a.worker)
    if a.baseline is None:p.error('--baseline required')
    children={}
    report=dict(passed=False,python=sys.version,platform=platform.platform(),baseline_pin='92f5213cf',
                rounds=21,aa_rounds=7,records=[],
                source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((ROOT/'fast/fastunknot').glob('*.py'))})
    def query(mode,key):
        child=children[mode];child.stdin.write(json.dumps(dict(id=key))+'\n');child.stdin.flush()
        return json.loads(child.stdout.readline())
    try:
        for mode,path in [('before',a.baseline),('control',a.baseline),('after',ROOT/'fast')]:
            children[mode]=subprocess.Popen([sys.executable,__file__,'--worker',str(path)],stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,text=True,env={**os.environ,'PYTHONHASHSEED':'0'})
        for key in IDS:
            for mode in children:query(mode,key)
            samples=[]
            for i in range(21):
                row={mode:query(mode,key) for mode in (('before','after') if i%2==0 else ('after','before'))}
                if row['before']['status']=='COMPLETE':
                    assert row['before']['certificate_sha256']==row['after']['certificate_sha256']
                samples.append(row)
            aa=[{mode:query(mode,key) for mode in (('before','control') if i%2==0 else ('control','before'))}
                for i in range(7)]
            record=dict(id=key,samples=samples,aa=aa,
                before_median=statistics.median(x['before']['total'] for x in samples),
                after_median=statistics.median(x['after']['total'] for x in samples),
                comparable=samples[0]['before']['status']==samples[0]['after']['status']=='COMPLETE',
                paired_latency_ratio=statistics.median(x['before']['total']/x['after']['total'] for x in samples),
                aa_ratio=statistics.median(x['before']['total']/x['control']['total'] for x in aa))
            report['records'].append(record)
            (DATA/'signed-annuli-benchmark-repeat.json').write_text(json.dumps(report,indent=2)+'\n')
            print(json.dumps({k:v for k,v in record.items() if k not in ('samples','aa')}),flush=True)
        report['passed']=True
        (DATA/'signed-annuli-benchmark-repeat.json').write_text(json.dumps(report,indent=2)+'\n')
    finally:
        for child in children.values():child.stdin.close();child.wait()

if __name__=='__main__':main()
