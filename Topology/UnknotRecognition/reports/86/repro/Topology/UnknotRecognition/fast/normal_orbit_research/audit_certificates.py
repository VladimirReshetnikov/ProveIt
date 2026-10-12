"""Cross-replay maintained and unchanged report-47 certificates and incidence.

Run from fast/: python -B normal_orbit_research/audit_certificates.py --output FILE
The archived producer and verifier load in a separate package namespace.
"""
import argparse
import hashlib
import importlib
import json
from pathlib import Path
import random
import sys
import types

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot.interval_orbits import IntervalPairing, count_orbits
from fastunknot.interval_orbit_verify import verify_orbit_certificate
from fastunknot.interval_incidence import analyze_port_incidence, verify_port_incidence_certificate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    archive = ROOT.parent/'reports/47/snapshot/Topology/UnknotRecognition/fast/fastunknot'
    package = types.ModuleType('_report47_orbit_audit')
    package.__path__ = [str(archive)]
    sys.modules[package.__name__] = package
    old = importlib.import_module(package.__name__+'.interval_orbits')
    old_check = importlib.import_module(package.__name__+'.interval_orbit_verify')
    old_incidence = importlib.import_module(package.__name__+'.interval_incidence')
    rng = random.Random(261008484)
    events = set()
    comparisons = incidence_comparisons = 0
    for case in range(1000):
        size = rng.randrange(1, 100)
        pairs, public = [], []
        for _ in range(rng.randrange(16)):
            width = rng.randrange(1, size+1)
            a, c = (rng.randrange(size-width+1) for _ in range(2))
            p = IntervalPairing(a, a+width-1, c, c+width-1, bool(rng.getrandbits(1)))
            pairs.append(p)
            public.append(dict(start=p.a, stop=p.b+1, sign=-1 if p.reverse else 1,
                               offset=p.a+p.d if p.reverse else p.c-p.a))
        reference = old.analyze_orbits(size, public, record_trace=True)
        classical = count_orbits(size, pairs, periodic_rule='aht', record_certificate=True)
        sharp = count_orbits(size, pairs, record_certificate=True)
        assert reference['orbit_count'] == classical.orbits == sharp.orbits
        assert verify_orbit_certificate(size, public, reference['certificate'])
        assert old_check.verify_orbit_certificate(size, public, classical.certificate)
        assert verify_orbit_certificate(size, pairs, sharp.certificate)
        events.update(e['op'] for e in sharp.certificate['operations'])
        comparisons += 1
        if case < 100:
            ports = [[sorted((rng.randrange(size+1), rng.randrange(size+1)))
                      for _ in range(rng.randrange(4))] for _ in range(rng.randrange(5))]
            before = old_incidence.analyze_port_incidence(size, public, ports, record_trace=True)
            after = analyze_port_incidence(size, pairs, ports, record_certificate=True)
            assert before['histogram'] == after['histogram']
            assert old_incidence.verify_port_incidence_certificate(size, public, ports,
                                                                    before['certificate'])
            assert verify_port_incidence_certificate(size, pairs, ports, after['certificate'])
            incidence_comparisons += 1
    assert events == {'delete', 'contract', 'trim', 'merge', 'transmit', 'truncate'}
    paths = [ROOT/'fastunknot'/name for name in
             ('interval_orbits.py', 'interval_orbit_verify.py', 'interval_incidence.py')]
    paths += [archive/name for name in ('interval_orbits.py', 'interval_orbit_verify.py',
              'interval_incidence.py', 'normal_components.py', 'normal_interval_extraction.py',
              'integer_codec.py')]
    paths += [Path(__file__).resolve()]
    result = dict(seed=261008484, orbit_systems=comparisons,
                  cross_replay_directions=['report47_v1_to_maintained', 'maintained_v1_to_report47'],
                  sharp_replays=comparisons, local_operations=sorted(events),
                  incidence_comparisons=incidence_comparisons,
                  source_sha256={str(p.relative_to(ROOT.parent)):hashlib.sha256(p.read_bytes()).hexdigest()
                                 for p in paths})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key:value for key,value in result.items() if key!='source_sha256'}))


if __name__ == '__main__':
    main()
