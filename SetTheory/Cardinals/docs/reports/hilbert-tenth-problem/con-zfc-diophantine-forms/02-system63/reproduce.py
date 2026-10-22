#!/usr/bin/env python3
"""Reproduce finite checks without expanding the enormous K215 coefficients.

Runs offline with Python's standard library. Recorded deliverables are not
modified; generated control files are written to a temporary directory.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def call(script, *args):
    result = subprocess.run([sys.executable, str(HERE/script), *map(str,args)],
                            cwd=HERE, capture_output=True, text=True, timeout=180)
    if result.returncode:
        raise RuntimeError(script + ' failed:\n' + result.stdout + result.stderr)
    packet = json.loads(result.stdout)
    require(str(packet.get('status', '')).lower().startswith('pass'),
            script + ' returned a nonpassing status')
    print('PASS ' + script, flush=True)
    return packet


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, help='Optionally save the combined JSON receipt.')
    args = parser.parse_args()
    require(__debug__, 'Run without Python -O; the machine validator requires assertions.')
    manifest = json.loads((HERE/'PROVENANCE.json').read_text())
    source_count = 0
    for item in manifest['upstream_sources'] + manifest['preserved_notices_and_licenses']:
        raw = (HERE/item['copy_filename']).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == item['copy_sha256'],
                'provenance mismatch: ' + item['copy_filename'])
        source_count += 1
    print('PASS upstream source and notice hashes ('+str(source_count)+')', flush=True)
    checks = {}
    with tempfile.TemporaryDirectory(prefix='zfc-diophantine-check-') as directory:
        temp = Path(directory)
        checks['source_arithmetic'] = call('verify_square_marker.py')
        checks['independent_marker'] = call('check_square_marker_review.py',
            '--sources', HERE, '--receipt', temp/'marker-review.json')
        checks['machine_normalization'] = call('normalized_k215.py')
        checks['window_counts'] = call('check_window_count.py')
        checks['fixed_compiler'] = call('test_fixed_compiler.py')
        checks['quartic_generation'] = call('quadratic_lift.py',
            '--output', temp/'quartic.json', '--receipt', temp/'quartic-receipt.json')
        require((temp/'quartic.json').read_bytes() == (HERE/'quadratic_lift.json').read_bytes(),
                'quartic regenerated differently')
        checks['independent_quartic'] = call('check_quadratic_lift_review.py',
            '--source', HERE/'fixed_input63_ordinary_system.json',
            '--lift', HERE/'quadratic_lift.json', '--producer', HERE/'quadratic_lift.py',
            '--proof', HERE/'QUADRATIC_LIFT.md', '--receipt', temp/'quartic-review.json')
        checks['integer_domain'] = call('emit_sos_variants.py', '--output-directory', temp)
        for name in ('positive16_sos.json','integer64_sos.json'):
            require((temp/name).read_bytes() == (HERE/name).read_bytes(),
                    'regeneration mismatch: '+name)
    receipt = {'status':'PASS', 'source_snapshot':manifest['commit'],
               'source_and_notice_hashes_checked':source_count,
               'checks':checks,
               'actual_K215_window_list_enumerated':False,
               'actual_K215_giant_numerals_materialized':False,
               'new_Lean_or_Rocq_build':False,
               'scope':'Finite arithmetic, source and implementation checks; mathematical theorem in report.pdf.'}
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, indent=2)+'\n')
    print('All packaged checks passed. No consistency or nonhalting conclusion is inferred.')


if __name__ == '__main__':
    main()
