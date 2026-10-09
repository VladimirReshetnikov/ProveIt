"""Run in a real ProveIt checkout before promoting the additive adapter.

Usage: python integration/native_gate.py --fast-root /path/to/ProveIt/Topology/UnknotRecognition/fast
This gate uses the maintained weighted producer AND independent verifier, not
an API-shaped substitute. Missing native dependencies are NOT a passing run.
SPDX-License-Identifier: MIT-0
"""
import argparse
import copy
import hashlib
import json
import random
import sys
import time
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=ROOT/'results'/'native_gate.json')
    args = parser.parse_args()
    sys.path.insert(0, str(args.fast_root.resolve()))
    if not (args.fast_root/'fastunknot'/'weighted_orbits.py').is_file():
        parser.error('no native weighted_orbits.py at the supplied checkout; gate not run')
    from fastunknot.interval_orbits import IntervalPairing
    from fastunknot.weighted_orbits import weighted_orbit_histogram
    from compiled_ports.native import compile_profiles, verify_native_certificate
    from compiled_ports.reference import literal_profiles
    from compiled_ports.profiles import Profiles, json_safe
    from compiled_ports.programs import ConeProgram
    from compiled_ports.verify import verify_change_points
    rng = random.Random(261008641)
    count = certificates = mutations = 0
    started = time.perf_counter()
    for _ in range(200):
        size = rng.randrange(1, 50)
        cuts = [0] + sorted(rng.sample(range(1, size), rng.randrange(min(size, 9)))) + [size]
        rows = []
        for _ in range(rng.randrange(9)):
            width = rng.randrange(1, size+1)
            a, c = rng.randrange(size-width+1), rng.randrange(size-width+1)
            rows.append((a, a+width-1, c, c+width-1, bool(rng.randrange(2))))
        pairs = [IntervalPairing(*p) for p in rows]
        expected = literal_profiles(size, rows, cuts)
        dim = len(cuts)-1
        weights = [(cuts[i], cuts[i+1], [int(i == j) for j in range(dim)]) for i in range(dim)]
        vector = weighted_orbit_histogram(size, pairs, weights, dimension=dim)
        assert vector['status'] == 'COMPLETE'
        vector_table = Profiles.from_histogram(expected.lengths,
                      {tuple(row['weight']): row['orbits'] for row in vector['histogram']})
        assert vector_table == expected
        for mode in ('binary', 'mixed'):
            answer = compile_profiles(size, pairs, cuts, packing=mode, record_certificate=True)
            assert answer['profiles'] == expected
            trusted = verify_native_certificate(size, pairs, cuts, answer['certificate'])
            assert trusted == expected
            certificates += 1
            p = ConeProgram(dim, [dict(op='cone', atoms=list(range(dim)))])
            assert verify_change_points(trusted, p.to_records(), p.root, p.change_points(trusted)['events'])
            altered = copy.deepcopy(answer['certificate'])
            altered['size'] += 1
            try:
                verify_native_certificate(size, pairs, cuts, altered)
            except ValueError:
                mutations += 1
            else:
                raise AssertionError('source mutation accepted')
            count += 1
    # A genuinely compressed pairing system: q parallel copies of a path
    # across eight atoms; no point expansion, no literal expected oracle.
    q, m = 1 << 1024, 8
    cuts = [j*q for j in range(m+1)]
    pairs = [IntervalPairing(0, q-1, j*q, (j+1)*q-1) for j in range(1, m)]
    expected = Profiles.from_histogram((q,)*m, {(1,)*m: q})
    for mode in ('binary', 'mixed'):
        answer = compile_profiles(m*q, pairs, cuts, packing=mode, record_certificate=True)
        assert answer['profiles'] == expected
        assert verify_native_certificate(m*q, pairs, cuts, answer['certificate']) == expected
        certificates += 1
        count += 1
    out = dict(status='PASS', seed=261008641, comparisons=count,
               source_bound_replays=certificates, source_mutations_rejected=mutations,
               seconds=time.perf_counter()-started, python=sys.version,
               note='This is a focused native gate, not the complete maintained test suite.',
               source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in sorted((args.fast_root/'fastunknot').glob('*.py'))})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(json_safe(out), indent=2)+'\n')
    print(json.dumps({k: v for k, v in out.items() if k != 'source_sha256'}, indent=2))

if __name__ == '__main__':
    main()
