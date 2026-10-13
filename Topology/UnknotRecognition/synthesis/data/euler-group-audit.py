"""Separate-process compatibility and source replay, with a literal new-case oracle.

Baseline is a git archive of 02f95a64a, selected explicitly with --baseline.
Timing fields in this correctness audit are deliberately omitted.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
DATA = Path(__file__).parent
PIN = '02f95a64a'


def worker(fast):
    sys.path.insert(0, str(fast))
    from fastunknot.integer_codec import json_safe
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    for line in sys.stdin:
        case = json.loads(line)
        r = normal_cut_handlebodies(case['triangulation'], case['coordinates'], record_certificate=True)
        answer = dict(id=case['id'], status=r['status'], reason=r.get('reason'))
        if r['status'] == 'COMPLETE':
            assert verify_normal_cut_handlebodies(case['triangulation'], case['coordinates'], r['certificate'])
            packet = json.dumps(json_safe(r['certificate']), sort_keys=True, separators=(',', ':')).encode()
            answer.update(replayed=True, certificate_sha256=hashlib.sha256(packet).hexdigest(),
                          certificate_bytes=len(packet), histogram=r['census']['histogram'],
                          schema=r['certificate']['schema'])
        print(json.dumps(json_safe(answer)), flush=True)


def main():
    p = argparse.ArgumentParser(); p.add_argument('--worker', type=Path); p.add_argument('--baseline', type=Path)
    a = p.parse_args()
    if a.worker: return worker(a.worker)
    if a.baseline is None: p.error('--baseline required')
    cases = [c for name in ('corpus.json','three_handle_corpus.json')
             for c in json.loads((ROOT/'fast/marked_parallelity_research'/name).read_text())['cases']]
    processes = {}
    report = dict(baseline_pin=PIN, records=[], passed=False,
                  source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in sorted((ROOT/'fast/fastunknot').glob('*.py'))})
    try:
        for mode, fast in [('before', a.baseline), ('after', ROOT/'fast')]:
            processes[mode] = subprocess.Popen([sys.executable, __file__, '--worker', str(fast)],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
        for case in cases:
            row = dict(id=case['id'])
            for mode, process in processes.items():
                process.stdin.write(json.dumps(case)+'\n'); process.stdin.flush()
                line = process.stdout.readline()
                if not line: raise RuntimeError('worker stopped: '+mode)
                row[mode] = json.loads(line)
            if row['before']['status'] == 'COMPLETE':
                assert row['after']['status'] == 'COMPLETE', row['id']
                assert row['before']['certificate_sha256'] == row['after']['certificate_sha256'], row['id']
            report['records'].append(row)
            (DATA/'euler-group-audit.json').write_text(json.dumps(report, indent=2)+'\n')
            print(len(report['records']), row['id'], row['before']['status'],row['after']['status'],flush=True)
        sys.path.insert(0,str(ROOT/'fast'))
        from normal_orbit_research.fixtures import regina_surface, regina_triangulation
        added = [r['id'] for r in report['records'] if r['before']['status'] != 'COMPLETE' and r['after']['status'] == 'COMPLETE']
        oracles=[]
        for key in added:
            c=next(c for c in cases if c['id']==key)
            s=regina_surface(regina_triangulation(c['triangulation']),c['coordinates'])
            cut=s.cutAlong(); pieces=cut.triangulateComponents()
            histogram=[dict(genus=g,multiplicity=n) for g,n in sorted(Counter(p.recogniseHandlebody() for p in pieces).items())]
            expected=next(r for r in report['records'] if r['id']==key)['after']['histogram']
            assert histogram==expected,(key,histogram,expected)
            oracles.append(dict(id=key,tetrahedra=cut.size(),histogram=histogram))
        report.update(passed=True, cases=len(cases), before=sum(r['before']['status']=='COMPLETE' for r in report['records']),
                      after=sum(r['after']['status']=='COMPLETE' for r in report['records']), added=added,literal_oracles=oracles)
        (DATA/'euler-group-audit.json').write_text(json.dumps(report,indent=2)+'\n')
    finally:
        for process in processes.values():
            process.stdin.close(); process.wait()

if __name__=='__main__': main()
