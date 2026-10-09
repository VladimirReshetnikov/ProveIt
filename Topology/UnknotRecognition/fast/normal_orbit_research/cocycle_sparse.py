"""Compare sparse cocycle pivots with the published left-to-right solver."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import subprocess
import time
from types import ModuleType
from unittest.mock import patch

from fastunknot import Diagram, recognize
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.diagram_exterior_verify import verify_diagram_exterior
from fastunknot.normal_cocycle import rank_one_cocycle_seed
from fastunknot.normal_seed import normal_seed_decide
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from normal_orbit_research import seeds

BASELINE = '7a13523cca5a23de7eb3ca143d630ed0b952bdcf'
ROOT = Path(__file__).resolve().parents[1]
AUDIT = ROOT.parent/'synthesis/data/cocycle-seed-audit.json'


def baseline():
    path = 'Topology/UnknotRecognition/fast/fastunknot/normal_cocycle.py'
    source = subprocess.check_output(['git', 'show', BASELINE+':'+path], cwd=ROOT)
    module = ModuleType('_cocycle_sparse_baseline')
    module.__package__ = 'fastunknot'
    exec(compile(source, BASELINE+':'+path, 'exec'), module.__dict__)
    return module.rank_one_cocycle_seed, sha256(source).hexdigest()


def pins():
    result = seeds.sources()
    result[str(AUDIT.relative_to(ROOT.parent))] = sha256(AUDIT.read_bytes()).hexdigest()
    return result


def audit(old):
    previous = json.loads(AUDIT.read_text())
    records = []
    for entry in previous['cases']:
        source = entry['source']
        diagram = Diagram.from_pd(source['pd'])
        raw = diagram_exterior(diagram)
        before, after = old(raw), rank_one_cocycle_seed(raw)
        for key in ('vertices', 'heights', 'coordinates'):
            assert before[key] == after[key], (source['name'], key)
        _coordinates(_prepare(raw, lambda: None), after['coordinates'], lambda: None)
        result = normal_seed_decide(diagram)
        if result['status'] == 'UNKNOT':
            assert source['expected'] == 'UNKNOT'
            assert verify_normal_seed_certificate(diagram, result['certificate'])
            result['certificate_sha256'] = seeds.digest(result.pop('certificate'))
            if entry['result']['status'] == 'UNKNOT':
                assert result['certificate_sha256'] == entry['result']['certificate_sha256']
        if entry['result']['status'] == 'UNKNOT':
            assert result['status'] == 'UNKNOT'
        records.append(dict(name=source['name'], expected=source['expected'],
                            old_cocycle=before['stats'], new_cocycle=after['stats'],
                            old_status=entry['result']['status'], result=result))
        print(source['name'], before['stats']['eliminations'], after['stats']['eliminations'],
              result['status'], flush=True)
    return dict(cases=records, identical_seed_count=len(records),
                source_replays=sum(r['result']['status'] == 'UNKNOT' for r in records))


def benchmark(old, count, mode):
    corpus = {r['name']: r['pd'] for r in seeds.harness.corpus()}
    if mode == 'prepare':
        cases = [(f'circle-{n}', Diagram.from_braid(n+1, list(range(1, n+1))).pd)
                 for n in (1, 8, 32, 64)]
        cases += [(name, corpus[name]) for name in ('survivor-00', 'gordian')]
        def run(pd, use_old):
            diagram = Diagram.from_pd(pd)
            raw = diagram_exterior(diagram)
            assert verify_diagram_exterior(diagram, raw)
            seed = (old if use_old else rank_one_cocycle_seed)(raw)
            _coordinates(_prepare(raw, lambda: None), seed['coordinates'], lambda: None)
            return dict(completed=True, stats=seed['stats'],
                        seed_sha256=seeds.digest({k: seed[k] for k in ('vertices', 'heights', 'coordinates')}))
    else:
        cases = [('circle-8', Diagram.from_braid(9, list(range(1, 9))).pd),
                 ('circle-16', Diagram.from_braid(17, list(range(1, 17))).pd),
                 ('optimized-positive', Diagram.from_braid(4, [-1, 2, 1, -2, 3]).pd),
                 ('genus-one-miss', Diagram.from_braid(2, [1, 1, -1]).pd),
                 ('trefoil', Diagram.from_braid(2, [1, 1, 1]).pd)]
        def run(pd, use_old):
            with patch('fastunknot.normal_seed.rank_one_cocycle_seed', old if use_old else rank_one_cocycle_seed):
                result = recognize(Diagram.from_pd(pd), **seeds.FORCED)
            expected = 'KNOTTED' if pd == cases[-1][1] else 'UNKNOT'
            assert result.status == expected
            native = result.evidence['normal_seed']
            return dict(completed=True, status=result.status, method=result.method,
                        native_status=native['status'], native_work=native['work'],
                        cocycle=native['stats']['cocycle'])
    return seeds.rounds(cases, run, count)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'prepare', 'recognize'))
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old, old_hash = baseline()
    before = pins()
    start = time.perf_counter()
    result = audit(old) if args.mode == 'audit' else benchmark(old, args.rounds, args.mode)
    elapsed = time.perf_counter()-start
    assert pins() == before
    result.update(mode=args.mode, elapsed_seconds=elapsed, source_sha256=before,
                  baseline_commit=BASELINE, baseline_module_sha256=old_hash,
                  python=platform.python_version(), platform=platform.platform(), seed=seeds.SEED+4)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(args.mode, 'complete', elapsed, flush=True)


if __name__ == '__main__':
    main()
