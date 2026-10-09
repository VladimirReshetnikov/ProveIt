"""Run this in a real ProveIt checkout; NOT executed in the delivery audit.

Usage: python integration/native_smoke.py /path/to/ProveIt --cases 250
This imports the maintained modules, compares dense and sparse profiles,
and replays genuine native AHT certificates. No ordinary dispatch is changed.
"""
import argparse
from pathlib import Path
import random
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('repository', type=Path)
    parser.add_argument('--cases', type=int, default=250)
    args = parser.parse_args()
    fast = args.repository / 'Topology/UnknotRecognition/fast'
    if not (fast / 'fastunknot/interval_orbits.py').is_file():
        parser.error('repository must contain the maintained interval-orbit modules')
    if args.cases < 1:
        parser.error('cases must be positive')
    sys.path.insert(0, str(fast))
    from fastunknot.interval_orbits import IntervalPairing
    from fastunknot.interval_incidence import analyze_port_incidence
    from sparse_ports.proveit import (
        analyze_port_incidence_sparse, verify_sparse_port_incidence_certificate)
    from sparse_ports.codec import dumps, loads
    rng = random.Random(261008507)
    for index in range(args.cases):
        n, r = rng.randrange(1, 61), rng.randrange(9)
        pairs = []
        for _ in range(rng.randrange(11)):
            width = rng.randrange(1, n + 1)
            a, c = rng.randrange(n - width + 1), rng.randrange(n - width + 1)
            pairs.append(IntervalPairing(a, a + width - 1, c, c + width - 1,
                                         bool(rng.randrange(2))))
        ports = [[tuple(sorted((rng.randrange(n + 1), rng.randrange(n + 1))))
                  for _ in range(rng.randrange(3))] for _ in range(r)]
        dense = analyze_port_incidence(n, pairs, ports, max_ports=r)
        sparse = analyze_port_incidence_sparse(n, pairs, ports, record_certificate=True)
        assert dense['status'] == sparse['status'] == 'COMPLETE', index
        expected = {t: w for t, w in enumerate(dense['histogram']) if w}
        assert dict(sparse['histogram']) == expected, index
        certificate = loads(dumps(sparse['certificate']))
        assert verify_sparse_port_incidence_certificate(n, pairs, ports, certificate), index
        # Independently verify after disabling the producer namespace.
        import fastunknot.interval_orbits as producer
        original = producer.count_orbits
        try:
            def forbidden(*_a, **_k):
                raise AssertionError('verifier called the orbit producer')
            producer.count_orbits = forbidden
            assert verify_sparse_port_incidence_certificate(n, pairs, ports, certificate)
        finally:
            producer.count_orbits = original
    print(f'PASS: {args.cases} genuine maintained-kernel integration cases')


if __name__ == '__main__':
    main()
