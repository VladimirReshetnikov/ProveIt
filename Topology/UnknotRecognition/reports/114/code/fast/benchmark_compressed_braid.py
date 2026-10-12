"""Paired explicit/compressed braid timings, including native proof replay."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import time

from fastunknot.braid import braid_certificate
from fastunknot.compressed_braid import Builder, recognize
from fastunknot.compressed_braid.grammar import expand, validate
from compressed_braid_research.families import sleeve, singleton_forest

ROOT = Path(__file__).resolve().parent
CAP = 1 << 20


def sources():
    files = [Path(__file__).resolve(), ROOT/'fastunknot/braid.py',
             ROOT/'fastunknot/compressed_words.py',
             ROOT/'compressed_braid_research/families.py']
    files += sorted((ROOT/'fastunknot/compressed_braid').glob('*.py'))
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in files}


def measure(arms, expected, rng, rounds, batch):
    samples = {arm: [] for arm in arms}
    orders = []
    for trial in range(-1, rounds):
        order = list(arms)
        rng.shuffle(order)
        orders.append(order)
        for arm in order:
            start = time.perf_counter_ns()
            for _ in range(batch):
                status = arms[arm]()
            elapsed = (time.perf_counter_ns() - start) / (1e9 * batch)
            assert status == expected, (arm, status, expected)
            if trial >= 0:
                samples[arm].append(elapsed)
    return dict(seconds=samples, medians={k: median(v) for k, v in samples.items()},
                orders=orders, batch=batch,
                paired_ratios={k: median(x/y for x, y in zip(samples[next(iter(arms))], v))
                               for k, v in samples.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('positive rounds required')
    before = sources()
    rng = random.Random(261008491)
    cases = []
    for k in (0, 4, 8, 12, 16, 18, 64, 512, 4096):
        for negative in (False, True) if k <= 18 else (False,):
            cases.append((f'sleeve_{k}_{int(negative)}', sleeve(k, negative=negative),
                          'KNOTTED' if negative else 'UNKNOT'))
    # Uncompressed cancellation sleeves control for favorable grammar structure.
    for length in (20, 100, 500):
        word = [rng.choice((-2, -1, 1, 2)) for _ in range(length)]
        word += [1, 2] + [-g for g in reversed(word)]
        builder = Builder()
        cases.append((f'explicit_random_{length}', builder.data(builder.word(word)), 'UNKNOT'))
    for count in (4, 16):
        cases.append((f'forest_{count}', singleton_forest(count, 128), 'UNKNOT'))
    result = dict(schema='compressed_braid_benchmark_v1', seed=261008491,
                  python=platform.python_version(), platform=platform.platform(),
                  checkout=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  rounds=args.rounds, warmups=1, expansion_cap=CAP, cases=[],
                  scope='Same supplied grammar; explicit arm expands and calls maintained braid_certificate; native arm includes caps, proof production and independent replay. No PD conversion or whole-pipeline claim.')
    for name, data, expected in cases:
        print(name, flush=True)
        native = recognize(data)
        assert native['status'] == expected and native['verified']
        arms = {}
        length = validate(data).lengths[data['root']] if data['strands'] == 3 else None
        if length is not None and length <= CAP:
            def explicit():
                return braid_certificate(3, expand(data, limit=CAP))['status']
            arms.update(explicit=explicit, explicit_AA=explicit)
        def compressed():
            return recognize(data)['status']
        arms.update(native=compressed, native_AA=compressed)
        batch = 10 if length is not None and length < 2000 else 1
        row = measure(arms, expected, rng, args.rounds, batch)
        row.update(name=name, status=expected, strands=data['strands'],
                   rules=len(data['rules']), input_bytes=len(json.dumps(data).encode()),
                   expanded_length_hex=hex(length) if length is not None else None,
                   explicit_omitted_reason=None if 'explicit' in arms else
                       ('preflight expansion cap exceeded' if length is not None else 'forest: no matched complete explicit gateway'),
                   certificate_bytes=native['certificate_bytes'], resources=native['resources'])
        result['cases'].append(row)
    after = sources()
    assert before == after, 'sources changed during benchmark'
    result.update(source_sha256=before, sources_unchanged=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
