#!/usr/bin/env python3
"""Recorded finite expansion audit, independent of the histogram formulas."""
from __future__ import annotations
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import sys
import time
ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / 'src'), str(ROOT / 'tests')]
from affine_orbits import BulkIndex, SparseOverlay
from affine_orbits.certificate import make_certificate
from affine_orbits.checker import verify
from oracle import expanded
from test_affine import random_model, random_defect


def main() -> None:
    rng = random.Random(261009703)
    counts = Counter()
    started = time.perf_counter()
    for trial in range(2000):
        m = random_model(rng, W=rng.randrange(1, 51))
        index = BulkIndex(m)
        overlay = SparseOverlay(index)
        for _ in range(rng.randrange(21)):
            overlay.add(random_defect(rng, m))
            counts['pointwise_attachments'] += 1
        hist, labels, values = expanded(m, overlay.defects)
        assert hist == overlay.histogram
        assert len(values) == overlay.component_count
        counts['histogram_comparisons'] += 1
        for u in range(m.vertices):
            for x in range(m.sheets):
                assert overlay.weight(u, x) == values[labels[u * m.sheets + x]]
                counts['point_weight_comparisons'] += 1
        for _ in range(50):
            u, v = rng.randrange(m.vertices), rng.randrange(m.vertices)
            x, y = rng.randrange(m.sheets), rng.randrange(m.sheets)
            assert overlay.same_component(u, x, v, y) == (labels[u*m.sheets+x] == labels[v*m.sheets+y])
            counts['connectivity_comparisons'] += 1
        for val in hist:
            u, x = overlay.representative(val)
            assert values[labels[u*m.sheets+x]] == val
            counts['representative_checks'] += 1
        assert verify(m, overlay.defects, make_certificate(index, overlay))
        counts['certificate_replays'] += 1
        counts['models'] += 1
    out = dict(status='PASS', seed=261009703, counts=dict(counts),
               seconds=time.perf_counter()-started, python=platform.python_version(),
               source_hashes={str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
                              for p in sorted((ROOT/'src').rglob('*.py'))})
    (ROOT/'results/audit.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))

if __name__ == '__main__':
    main()
