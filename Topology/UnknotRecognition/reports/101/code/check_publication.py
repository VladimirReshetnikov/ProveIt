"""Replay retained examples, source/dependency hashes, and measurement accounting.

This does not rerun the timing experiments, the 448-case audit, or the upstream
ProveIt suite. Run tests/test_flags.py and code/audit.py for executable reruns.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
from statistics import median
import sys
from atlas import from_data, loads, digest, dumps, simplex
from flags import certificate_from_data, inventory
from replay import verify
from sources import tetrahedral_atlas, solid_torus_source, polytope_ball, product_with_line
from reference import compare_source_oracle
from morse_adapter import rm, convex_cone_certificate
ROOT = Path(__file__).resolve().parents[1]


def require(ok: bool, message: str) -> None:
    if not ok: raise ValueError(message)


def close(a: float, b: float) -> bool:
    return math.isclose(a, b, rel_tol=1e-12, abs_tol=1e-14)


def check_examples() -> list[dict]:
    results = []
    for path in sorted((ROOT/'examples').glob('*.json')):
        obj = loads(path.read_text())
        require(obj['schema'] == 'source-bound-flag-example-v1', 'bad example schema')
        source = from_data(obj['source_atlas'])
        certificate = certificate_from_data(obj['certificate'])
        mode = obj['mode']
        if mode == 'solid-torus':
            native = obj['source_specification']['tetrahedra']
            require(native == solid_torus_source(), 'wrong native fixture')
            require(obj['source_specification']['normal_coordinates'] == [[0]*7], 'not an empty native cut')
            rebuilt, metadata = tetrahedral_atlas(native)
            require(compare_source_oracle(native, metadata, certificate) == obj['literal_source_comparison'], 'source flag comparison differs')
        elif mode == 'periodic':
            n = (1 << obj['parameters']['bits']) + 1
            require(n == obj['source_specification']['segments'], 'periodic segment count differs')
            rebuilt = product_with_line(polytope_ball(simplex(2)), n, True)
        elif mode == 'convex':
            n = obj['parameters']['copies']
            require(n == obj['source_specification']['copies'], 'convex multiplicity differs')
            rebuilt = polytope_ball(simplex(3), n)
        else:
            raise ValueError('unknown controlled example source')
        require(rebuilt == source, 'retained atlas differs from controlled source')
        require(digest(source) == obj['source_sha256'], 'example source digest differs')
        require(verify(source, certificate), 'independent flag replay rejected')
        require(inventory(certificate.result) == obj['inventory'], 'example inventory differs')
        if mode == 'convex':
            packet, proof = rm.loads_certificate(obj['morse_certificate_json'])
            expected_packet, expected_proof, expected_counts = convex_cone_certificate(simplex(3), n, source, certificate)
            require(packet == expected_packet and proof == expected_proof, 'source-bound cone witness differs')
            require(tuple(obj['critical_cells']) == expected_counts, 'critical count differs')
            require(rm.verify_affine(rm.prepare(packet), proof), 'prior Morse checker rejected')
        results.append({'file':path.relative_to(ROOT).as_posix(),'mode':mode,'families':len(certificate.result.families),'replay':True})
    require(len(results) == 3, 'expected all three source-bound examples')
    return results


def check_measurements() -> dict:
    a = json.loads((ROOT/'results/audit.json').read_text())
    t = a['totals']
    require(len(a['one_tetra_cases']) == 145 == t['one_tetra_pairings_considered'], 'wrong source enumeration count')
    require(sum(r['accepted'] for r in a['one_tetra_cases']) == 70 == t['one_tetra_accepted_source_cases'], 'wrong accepted-source count')
    require(sum(not r['accepted'] for r in a['one_tetra_cases']) == 75 == t['one_tetra_rejected_face_holonomy'], 'wrong rejected-source count')
    require(len(a['literal_cases']) == 333 == t['convex_copy_cases']+t['seeded_product_cases'], 'literal case count differs')
    for key in ('cells','covers'):
        require(sum(r[key] for r in a['literal_cases']) == t['literal_compared_'+key], 'literal '+key+' accounting differs')
    require(t['symbolic_replays'] == 448 == 70+24+33+300+11+2*5, 'symbolic replay count differs')
    fixture = a['native_fixture']
    require(fixture['source'] == solid_torus_source(), 'audit source fixture differs')
    require(fixture['regular_cells']['cell_counts'] == [8,38,54,24], 'native regular cell counts differ')
    b = json.loads((ROOT/'results/benchmark.json').read_text())
    require(b['all_trials_finished'] and not b['knot_recognition_speedup_claimed'], 'incorrect benchmark scope')
    require(len(b['rows']) == 5 and len(b['samples']) == 30, 'wrong number of paired trials')
    for r in b['rows']:
        n = r['segments']
        all_samples = [s for s in b['samples'] if s['segments'] == n]
        require(sorted(s['trial'] for s in all_samples) == [-1,0,1,2,3,4], 'missing warmup or measured trial')
        samples = [s for s in all_samples if s['trial'] >= 0]
        for s in all_samples:
            require(sorted(s['order']) == ['encoded','literal_A','literal_B'], 'wrong trial arms')
            for arm in s['order']:
                require(s[arm]['cell_counts'] == [14*n,62*n,84*n,36*n], 'trial cell inventory differs')
                require(s[arm]['seconds'] > 0, 'nonpositive elapsed time')
            require(s['literal_A']['serialized_bytes'] == s['literal_B']['serialized_bytes'], 'A/A byte outputs differ')
        require(r['represented_cells'] == 196*n, 'total represented cells differ')
        computed = {
            'encoded_median_seconds':median(s['encoded']['seconds'] for s in samples),
            'literal_median_seconds':median(s['literal_A']['seconds'] for s in samples),
            'paired_literal_over_encoded':median(s['literal_A']['seconds']/s['encoded']['seconds'] for s in samples),
            'paired_A_over_B':median(s['literal_A']['seconds']/s['literal_B']['seconds'] for s in samples),
        }
        for key, value in computed.items(): require(close(r[key],value), key+' differs')
        require(r['encoded_bytes'] == samples[0]['encoded']['serialized_bytes'], 'encoded byte count differs')
        require(r['literal_bytes'] == samples[0]['literal_A']['serialized_bytes'], 'literal byte count differs')
    require([r['rank_bound_bits'] for r in b['binary_stress']] == [65,1025,4097,16385], 'binary stress sizes differ')
    for r in b['binary_stress']:
        require(len(r['seconds']) == 5 and close(r['median_seconds'],median(r['seconds'])), 'binary stress median differs')
        require((r['families'],r['charts']) == (196,1289), 'binary source expanded or changed structure')
    require('1024' in b['pilot_limitation'] and (ROOT/'results/benchmark_pilot_partial.txt').exists(), 'pilot limitation missing')
    log = (ROOT/'results/unit_tests.txt').read_text()
    require('Ran 32 tests' in log and log.rstrip().endswith('OK'), 'unit-test log is not the retained passing 32-test suite')
    require(16+3*30+25*52+291*11 == 4607, 'native family arithmetic differs')
    return {'counted_audit_replays':448,'retained_unit_tests':32,'paired_cases':5,'measured_paired_trials':25,'binary_stress_cases':4,'pilot_limitation_retained':True}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--require-manifest', action='store_true')
    args = parser.parse_args()
    try:
        provenance = json.loads((ROOT/'provenance/sources.json').read_text())
        for r in provenance['incoming_dependency']['files']:
            actual = hashlib.sha256((ROOT/r['delivered_path']).read_bytes()).hexdigest()
            require(actual == r['sha256'], 'retained predecessor bytes changed')
        require((ROOT/'article.pdf').read_bytes().startswith(b'%PDF-'), 'compiled article missing')
        for name in ('article.tex','README.md','SOURCE_AUDIT.md','INTEGRATION.md','SCHEMA.md','CLAIMS.md'):
            require((ROOT/name).is_file(), 'required artifact missing: '+name)
        result = {'examples':check_examples(),'evidence_accounting':check_measurements(),'dependency_hashes':True}
        manifest = ROOT/'MANIFEST.sha256'
        if args.require_manifest: require(manifest.is_file(),'package manifest missing')
        if manifest.is_file():
            lines = manifest.read_text().splitlines()
            seen = set()
            for line in lines:
                sha, name = line.split('  ',1)
                path = (ROOT/name).resolve()
                require(path.is_relative_to(ROOT) and path.is_file(), 'invalid manifest path')
                require(name not in seen, 'duplicate manifest path'); seen.add(name)
                require(hashlib.sha256(path.read_bytes()).hexdigest() == sha, 'manifest mismatch: '+name)
            result['manifest_files_checked'] = len(lines)
        result['status'] = 'PASS'
        result['scope'] = 'Replays retained examples and checks recorded evidence accounting; does not rerun the audit, timings or native suite.'
        print(json.dumps(result,indent=2))
        return 0
    except (ValueError,KeyError,TypeError,OSError) as exc:
        print('PUBLICATION CHECK FAILED: '+str(exc),file=sys.stderr)
        return 1

if __name__ == '__main__':
    raise SystemExit(main())
