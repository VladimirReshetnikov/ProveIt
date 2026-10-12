"""Separate-interpreter paired queries and complete corpus compatibility audit.

Run benchmark before other CPU-heavy validation. Workers time API production and
independent replay only; startup, JSON transport and source loading are excluded.
Both package copies are identical except four retained baseline modules.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import random
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
DATA = Path(__file__).parent
BASE = DATA / 'gap-prefix-baseline'
CORPORA = [ROOT / 'fast/marked_parallelity_research' / n
           for n in ('corpus.json', 'three_handle_corpus.json')]
IDS = ['pilot/lst_4_7/0', 'pilot/fibonacci_lst_08/0',
       'fibonacci_lst_09/mixed', 'pachner23_5_8_2/mixed']
SYNTHETIC = ['gaps32/count', 'gaps128/count', 'gaps256/count',
             'gaps128/weighted', 'gaps128/tagged', 'binary4096/tagged', 'dense/tagged']


def digest(data):
    return hashlib.sha256(data).hexdigest()


def pins():
    return {str(p.relative_to(ROOT / 'fast')): digest(p.read_bytes())
            for p in sorted((ROOT / 'fast/fastunknot').rglob('*.py'))}


def cases():
    return [c for p in CORPORA for c in json.loads(p.read_text())['cases']]


def worker(package):
    sys.path.insert(0, package)
    from fastunknot.integer_codec import json_safe
    from fastunknot.interval_orbits import IntervalPairing, count_orbits
    from fastunknot.interval_orbit_verify import verify_orbit_certificate
    from fastunknot.weighted_orbits import weighted_orbit_histogram
    from fastunknot.weighted_orbit_verify import verify_weighted_orbit_certificate
    from fastunknot.weighted_transversal import weighted_orbit_transversal
    from fastunknot.weighted_transversal_verify import verify_weighted_orbit_transversal
    from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
    from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
    bank = {c['id']: c for c in cases()}
    for line in sys.stdin:
        request = json.loads(line); key = request['id']
        if key in bank:
            c = bank[key]
            def produce():
                return normal_cut_handlebodies(c['triangulation'], c['coordinates'],
                                                record_certificate=True)
            def verify(proof):
                return verify_normal_cut_handlebodies(c['triangulation'], c['coordinates'], proof)
        else:
            source, kind = key.split('/')
            if source.startswith('gaps'):
                k = int(source[4:]); size = 8 * k + 3
                pairs = [IntervalPairing(8*i+1, 8*i+2, 8*i+5, 8*i+6, bool(i % 2))
                         for i in range(k)]
            elif source == 'binary4096':
                scale = 1 << 4096; size = 4 * scale
                pairs = [IntervalPairing(scale, scale+2, 3*scale, 3*scale+2, True)]
            else:
                size = 1000003
                pairs = [IntervalPairing(0, size-2, 1, size-1)]
            weights = [(0, size, (3, -5)), (size//3, 2*size//3, (-2, 7))]
            if kind == 'count':
                def produce():
                    a = count_orbits(size, pairs, record_certificate=True)
                    return dict(status='COMPLETE' if a.complete else 'INCONCLUSIVE', certificate=a.certificate)
                def verify(proof):
                    return verify_orbit_certificate(size, pairs, proof)
            else:
                prod, ver = ((weighted_orbit_histogram, verify_weighted_orbit_certificate)
                             if kind == 'weighted' else
                             (weighted_orbit_transversal, verify_weighted_orbit_transversal))
                def produce():
                    return prod(size, pairs, weights, dimension=2, record_certificate=True)
                def verify(proof):
                    return ver(size, pairs, weights, proof, dimension=2)
        start = time.perf_counter(); answer = produce(); produced = time.perf_counter()
        status = answer['status']; proof = answer.get('certificate')
        if status == 'COMPLETE':
            assert verify(proof), key
        end = time.perf_counter()
        payload = json.dumps(json_safe(proof), sort_keys=True, separators=(',', ':')).encode()
        result = dict(id=key, status=status, proof_sha256=digest(payload), proof_bytes=len(payload),
                      census=answer.get('census'), produce=produced-start, replay=end-produced,
                      total=end-start)
        print(json.dumps(json_safe(result)), flush=True)


class Workers:
    def __enter__(self):
        self.temp = tempfile.TemporaryDirectory(prefix='unknot-gap-prefix-')
        self.processes = {}
        for mode in ('before', 'after'):
            package = Path(self.temp.name) / mode
            shutil.copytree(ROOT / 'fast/fastunknot', package / 'fastunknot',
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            if mode == 'before':
                for p in BASE.glob('*.py'):
                    shutil.copy2(p, package / 'fastunknot' / p.name)
            self.processes[mode] = subprocess.Popen(
                [sys.executable, str(Path(__file__).resolve()), '--worker', str(package)],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
                env={**os.environ, 'PYTHONHASHSEED': '0'})
        return self

    def query(self, mode, key):
        p = self.processes[mode]
        p.stdin.write(json.dumps(dict(id=key)) + '\n'); p.stdin.flush()
        line = p.stdout.readline()
        if not line:
            raise RuntimeError(f'{mode} worker exited: {p.poll()}')
        return json.loads(line)

    def __exit__(self, *args):
        for p in self.processes.values():
            p.stdin.close()
            p.wait(timeout=30)
            p.stdout.close()
        self.temp.cleanup()


def main(mode):
    source_pins = pins(); target = DATA / f'gap-prefix-{mode}.json'
    report = dict(mode=mode, native_source_sha256=source_pins,
                  driver_sha256=digest(Path(__file__).read_bytes()),
                  baseline_sha256={p.name: digest(p.read_bytes()) for p in BASE.glob('*.py')},
                  corpus_sha256={p.name: digest(p.read_bytes()) for p in CORPORA},
                  python=sys.version, platform=platform.platform(), seed=261012106, cases=[])
    start_index = 0
    if mode == 'audit' and target.exists():
        previous = json.loads(target.read_text())
        assert not previous.get('finished'), 'audit already complete'
        for field in ('native_source_sha256', 'baseline_sha256', 'corpus_sha256'):
            assert previous[field] == report[field]
        start_index = len(previous['cases'])
        assert [c['id'] for c in previous['cases']] == [c['id'] for c in cases()][:start_index]
        report['cases'] = previous['cases']
        report['completed_prefix_driver_sha256'] = previous['driver_sha256']
        report['completed_prefix_cases'] = start_index
        report['resume_reason'] = 'Worker JSON response census exceeded the decimal digit cap; use the existing exact integer codec. Completed records retained unchanged.'
    rng = random.Random(report['seed'])
    with Workers() as w:
        for key in (SYNTHETIC + IDS if mode == 'benchmark' else [c['id'] for c in cases()][start_index:]):
            a = w.query('before', key); b = w.query('after', key)
            for field in ('status', 'proof_sha256', 'census'):
                assert a[field] == b[field], (key, field)
            rec = dict(id=key, status=a['status'], proof_sha256=a['proof_sha256'],
                       proof_bytes=a['proof_bytes'], identical_certificate=True)
            if mode == 'benchmark':
                assert a['status'] == 'COMPLETE', a
                samples, controls = [], []
                for _ in range(5):
                    order = ['before', 'after']; rng.shuffle(order); sample = dict(order=order)
                    for arm in order:
                        row = w.query(arm, key)
                        assert row['proof_sha256'] == a['proof_sha256']
                        sample[arm] = {n: row[n] for n in ('produce', 'replay', 'total')}
                    samples.append(sample)
                for _ in range(3):
                    first, second = (w.query('before', key) for _ in range(2))
                    controls.append(dict(first=first['total'], second=second['total'],
                                         ratio=first['total']/second['total']))
                rec.update(samples=samples, aa_samples=controls,
                           before_median=statistics.median(s['before']['total'] for s in samples),
                           after_median=statistics.median(s['after']['total'] for s in samples),
                           paired_speedup=statistics.median(s['before']['total']/s['after']['total'] for s in samples),
                           replay_speedup=statistics.median(s['before']['replay']/s['after']['replay'] for s in samples),
                           aa_median=statistics.median(s['ratio'] for s in controls))
            report['cases'].append(rec)
            target.write_text(json.dumps(report, indent=2) + '\n')
            print({k: v for k, v in rec.items() if k not in ('samples', 'aa_samples')}, flush=True)
    assert source_pins == pins()
    report['finished'] = True
    target.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--worker')
    parser.add_argument('--mode', choices=['benchmark', 'audit'], default='benchmark')
    args = parser.parse_args()
    if args.worker:
        worker(args.worker)
    else:
        main(args.mode)
