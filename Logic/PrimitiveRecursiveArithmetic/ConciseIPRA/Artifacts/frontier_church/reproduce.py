"""Verify the archive, incumbent measurements, and finite mathematical evidence.

This does not verify arbitrary lambda terms or rebuild the upstream Lean proof.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def script_json(relative):
    run = subprocess.run([sys.executable, str(ROOT / relative)],
                         text=True, capture_output=True, timeout=60)
    require(run.returncode == 0, relative + ': ' + run.stderr)
    return json.loads(run.stdout)


def verify_checks():
    measurements = script_json('code/measure.py')
    require(measurements['all_match'],
            'Incumbent metrics differ; use the recorded CPython/zlib runtime.')
    require(measurements['all_gzip_members_verified'], 'Compressed source mismatch')
    for row in measurements['profiles']:
        require(row['stored_gzip_is_reproduced_exactly'], 'Gzip encoding differs')
    model = script_json('code/verify_church_obstruction.py')
    require(model['status'] == 'PASS', 'Church model check failed')
    run = subprocess.run([sys.executable, str(ROOT / 'code/search_three_cycle.py')],
                         text=True, capture_output=True, timeout=60)
    require(run.returncode == 0, 'Finite syntax search failed: ' + run.stderr)
    search = [json.loads(line) for line in run.stdout.splitlines() if line]
    expected = [json.loads(line) for line in
                (ROOT / 'evidence/three_cycle_search.jsonl').read_text().splitlines()]
    require(search == expected, 'Finite syntax search record differs')
    return {
        'status': 'PASS',
        'incumbent_profiles_remeasured': len(measurements['profiles']),
        'gzip_members_verified': len(measurements['profiles']),
        'ground_endomaps_checked': len(model['ground_endomaps']),
        'predicate_subsets_checked': len(model['all_subsets_checked_for_induction']),
        'general_endomap_counts': [x['endomaps_checked']
                                  for x in model['generalized_finite_examples']],
        'native_syntax_terms_enumerated': sum(x['count'] for x in search),
        'three_cycle_search_scope': 'Reproduction of an existing result, not a new reduction',
        'proof_scope': 'Finite computations plus measurements; universal mathematical claims have written proofs',
        'qualifying_new_axiomatization_obtained': False,
    }


def verify_manifest():
    count = 0
    for line in (ROOT / 'MANIFEST.sha256').read_text().splitlines():
        digest, name = line.split('  ', 1)
        path = ROOT / name
        require(path.is_file(), 'Missing file: ' + name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest,
                'Hash mismatch: ' + name)
        count += 1
    return count


if __name__ == '__main__':
    require(__debug__, 'Run without -O or -OO: finite checks use assertions.')
    count = verify_manifest()
    result = verify_checks()
    result['manifest_files_checked'] = count
    print(json.dumps(result, indent=2))
