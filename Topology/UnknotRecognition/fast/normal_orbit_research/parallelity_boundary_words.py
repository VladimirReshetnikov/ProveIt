"""Reproducible binary-multiplicity benchmark for ordered core interfaces.

Run from fast/: python -m normal_orbit_research.parallelity_boundary_words
    --output boundary-words-benchmark.json
The cases are actual layered-solid-torus normal coordinates. Every produced
certificate is independently replayed. Timings concern this new operator only.
"""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import sys
from time import perf_counter

from fastunknot.integer_codec import json_safe
from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words
from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words
from normal_orbit_research.fixtures import layered_torus


def benchmark():
    results = []
    for tetrahedra in (1, 2, 4, 8):
        raw, base = layered_torus(tetrahedra)
        for exponent in (0, 16, 64, 256, 1024, 4096, 16384):
            factor = 1 << exponent
            rows = [[factor * value for value in row] for row in base]
            start = perf_counter()
            answer = normal_parallelity_boundary_words(raw, rows, record_certificate=True)
            generated = perf_counter() - start
            proof = answer['certificate']
            start = perf_counter()
            verified = verify_parallelity_boundary_words(raw, rows, proof)
            replayed = perf_counter() - start
            if not verified:
                raise AssertionError('independent boundary-word replay failed')
            skeleton = answer['skeleton']
            serialized = json.dumps(json_safe(proof), sort_keys=True, separators=(',', ':')).encode()
            record = dict(tetrahedra=tetrahedra, multiplicity_exponent=exponent,
                          normal_disc_count_bits=sum(sum(row) for row in rows).bit_length(),
                          ports=len(skeleton['ports']), gaps=len(skeleton['gaps']),
                          boundary_loops=len(skeleton['boundary_loops']),
                          interval_attachments=skeleton['interval_attachments'],
                          circle_attachments=skeleton['circle_attachments'],
                          producer_seconds=generated, verifier_seconds=replayed,
                          certificate_bytes=len(serialized),
                          certificate_sha256=hashlib.sha256(serialized).hexdigest(),
                          independently_verified=True, query_stats=answer['stats'])
            results.append(record)
            print(json.dumps({k: record[k] for k in ('tetrahedra', 'multiplicity_exponent',
                             'ports', 'interval_attachments', 'producer_seconds', 'verifier_seconds')}),
                  flush=True)
    root = Path(__file__).resolve().parents[1]
    files = ('fastunknot/parallelity_boundary_words.py',
             'fastunknot/parallelity_boundary_words_verify.py',
             'fastunknot/normal_parallelity_geometry.py',
             'fastunknot/normal_parallelity_reference.py',
             'fastunknot/weighted_orbits.py', 'fastunknot/weighted_orbit_verify.py',
             'fastunknot/interval_orbits.py', 'fastunknot/interval_orbit_verify.py',
             'normal_orbit_research/fixtures.py',
             'normal_orbit_research/parallelity_boundary_words.py')
    return dict(schema='parallelity-boundary-words-benchmark-v1', python=sys.version,
                platform=platform.platform(),
                source_sha256={p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in files},
                cases=results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = benchmark()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(report), indent=2) + '\n')


if __name__ == '__main__':
    main()
