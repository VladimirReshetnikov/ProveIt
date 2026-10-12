"""Check distributed hashes, raw benchmark arithmetic, and saved proof replay.

Run from any directory: python verify_artifacts.py
No search, source graph expansion, NetworkX, or native recognizer is needed.
"""
from __future__ import annotations

import hashlib
import json
import math
from pathlib import Path
import statistics
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'code'))
from pattern_kernel.core import Block, Tile, natural
from pattern_kernel.verify import verify_result, verify_source_witness


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load_chain(path: Path) -> tuple[Block, ...]:
    obj = json.loads(path.read_text())
    require(obj.get('schema') == 'closed-tile-chain-v1', 'wrong input schema')
    blocks = []
    for record in obj['blocks']:
        t = record['tile']
        tile = Tile(t['n'], tuple(tuple(e) for e in t['edges']),
                    tuple(t['left']), tuple(t['right']))
        blocks.append(Block(tile, natural(record['copies'])))
    return tuple(blocks)


def same(a: float, b: float, label: str) -> None:
    require(math.isclose(a, b, rel_tol=1e-12, abs_tol=1e-12), label)


def main() -> None:
    manifest = ROOT / 'SHA256SUMS'
    require(manifest.is_file(), 'SHA256SUMS is missing')
    count = 0
    for line in manifest.read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = (ROOT / name).resolve()
        require(path.is_relative_to(ROOT), 'hash path escapes package')
        require(path.is_file(), f'missing artifact: {name}')
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == digest, f'artifact hash mismatch: {name}')
        count += 1

    replayed = {}
    for name in ('huge_prism', 'huge_triangle_defect'):
        chain = load_chain(ROOT / 'examples' / f'{name}.json')
        proof = json.loads((ROOT / 'examples' / f'{name}_proof.json').read_text())
        require(verify_result(chain, proof), f'proof rejected: {name}')
        replayed[name] = proof['graph_proof']['verdict']
        if 'source_witness' in proof:
            addresses = verify_source_witness(chain, proof['source_witness'])
            saved = json.loads((ROOT / 'examples' /
                               f'{name}_source_addresses.json').read_text())
            require(addresses == saved, 'original edge addresses disagree')

    audit = json.loads((ROOT / 'experiments' / 'audit.json').read_text())
    require(audit['all_passed'], 'audit did not pass')
    require(audit['four_copy_signature_comparisons'] == 6000,
            'unexpected signature audit count')
    require(audit['native_recognizer_regression'] == 'NOT_RUN',
            'unexpected native regression claim')
    bench = json.loads((ROOT / 'experiments' / 'benchmark.json').read_text())
    require([r['copies'] for r in bench['rows']] == [1, 3, 4, 8, 16, 32],
            'unexpected benchmark cases')
    for row in bench['rows']:
        samples = row['samples']
        require(len(samples) == bench['rounds'] == 5, 'missing benchmark round')
        require(sorted(s['round'] for s in samples) == list(range(5)),
                'duplicate or missing round index')
        for s in samples:
            require(sorted(s['order']) == ['explicit', 'kernel'], 'bad arm order')
            same(s['ratio'], s['explicit_ms'] / s['kernel_ms'], 'paired ratio')
        for key, sample_key in (('explicit_median_ms', 'explicit_ms'),
                                ('kernel_median_ms', 'kernel_ms'),
                                ('median_paired_ratio', 'ratio')):
            same(row[key], statistics.median(s[sample_key] for s in samples), key)
    control = bench['identical_explicit_control']
    for s in control:
        same(s['ratio'], s['a_ms'] / s['b_ms'], 'A/A ratio')
    same(bench['control_median_ratio'], statistics.median(s['ratio'] for s in control),
         'A/A median')
    for row in bench['large_binary_cases']:
        same(row['kernel_median_ms'], statistics.median(row['samples_ms']),
             'large-binary median')
    require(bench['native_recognizer_benchmark'] == 'NOT_RUN',
            'unexpected native benchmark claim')
    print(json.dumps({'verified_artifact_hashes': count, 'proof_replay': replayed,
                      'benchmark_arithmetic': 'PASS',
                      'native_recognizer_run': False}, indent=2))


if __name__ == '__main__':
    main()
