"""Run from the repository root after tests finish; compare complete cut queries.

Includes production plus independent replay, five shuffled pairs, and identical
explicit-cut controls. This is neither discovery nor full knot recognition.
"""
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'fast'))
from fastunknot.integer_codec import json_safe
from marked_parallelity_research.benchmark_census import explicit, native
from normal_orbit_research.seeds import sources


def main():
    import regina
    pins = sources()
    corpus_path = ROOT / 'fast/marked_parallelity_research/corpus.json'
    corpus = json.loads(corpus_path.read_text())['cases']
    report = dict(native_source_sha256=pins, python=sys.version,
                  regina=regina.versionString(), platform=platform.platform(),
                  driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                  corpus_sha256=hashlib.sha256(corpus_path.read_bytes()).hexdigest(),
                  seed=852026, rounds=5, cases=[], capacity=[])
    rng = random.Random(report['seed'])
    output = Path(__file__).with_suffix('.json')
    for t in (2, 3):
        role = 'new_disk_absorption' if t == 2 else 'existing_v1_control'
        c = next(c for c in corpus if c['id'] == f'pilot/fibonacci_lst_{t:02d}/0')
        for copies in (1, 16, 256, 4096):
            raw = c['triangulation']
            rows = [[copies * x for x in row] for row in c['coordinates']]
            reference, _ = explicit(raw, rows)
            result, _ = native(raw, rows)
            expected = reference['histogram']
            assert result['census']['histogram'] == expected
            samples = []
            for _ in range(report['rounds']):
                order = ['native', 'explicit']
                rng.shuffle(order)
                sample = dict(order=order)
                for name in order:
                    if name == 'native':
                        result, timing = native(raw, rows)
                        assert result['census']['histogram'] == expected
                    else:
                        value, timing = explicit(raw, rows)
                        assert value['histogram'] == expected
                    sample[name] = timing
                samples.append(sample)
            aa = []
            for _ in range(3):
                _, first = explicit(raw, rows)
                _, second = explicit(raw, rows)
                aa.append(first / second)
            data = dict(source=c['id'], role=role, schema=result['certificate']['schema'],
                        tetrahedra=t, copies=copies,
                        normal_disks=sum(map(sum, rows)), histogram=expected,
                        explicit_cut_tetrahedra=reference['tetrahedra'],
                        native_median=statistics.median(s['native']['total'] for s in samples),
                        explicit_median=statistics.median(s['explicit'] for s in samples),
                        median_paired_ratio=statistics.median(s['explicit'] / s['native']['total'] for s in samples),
                        samples=samples, aa_ratios=aa, aa_median=statistics.median(aa))
            report['cases'].append(data)
            print(json.dumps({k: v for k, v in data.items() if k not in ('samples', 'aa_ratios')}), flush=True)
            output.write_text(json.dumps(json_safe(report), indent=2) + '\n')
        rows = [[(1 << 16384) * x for x in row] for row in c['coordinates']]
        result, timing = native(raw, rows)
        encoded = json.dumps(json_safe(result['certificate']), sort_keys=True).encode()
        data = dict(source=c['id'], role=role, schema=result['certificate']['schema'],
                    tetrahedra=t, multiplicity_power=16384,
                    census=result['census']['histogram'], timing=timing,
                    certificate_bytes=len(encoded),
                    certificate_sha256=hashlib.sha256(encoded).hexdigest(),
                    absorbed_components=len(result['certificate'].get('absorption', {}).get('components', [])))
        report['capacity'].append(data)
        print(json.dumps({k: v for k, v in data.items() if k != 'census'}), flush=True)
        output.write_text(json.dumps(json_safe(report), indent=2) + '\n')
    assert sources() == pins, 'native source changed during benchmark'


if __name__ == '__main__':
    main()
