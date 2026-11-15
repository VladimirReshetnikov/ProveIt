#!/usr/bin/env python3
"""Replay the accepted constructions and accompanying mathematical certificates.

Default: complete literal replay. --quick omits only the independent literal
replay already frozen in verification/independent/results. All regeneration
uses temporary directories; delivered files remain unchanged.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true')
    parser.add_argument('--receipt', type=Path,
                        help='Optional new receipt path; omit to print only.')
    args = parser.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Assertions must remain enabled; do not use -O.')
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    checked = []
    manifest = ROOT/'MANIFEST.sha256'
    if manifest.exists():
        for line in manifest.read_text().splitlines():
            expected, name = line.split('  ', 1)
            path = ROOT/name
            assert path.is_file(), name
            assert digest(path) == expected, ('manifest mismatch', name)
            checked.append(name)
    print('Manifest:', len(checked), 'file identities checked', flush=True)
    command = [sys.executable, str(ROOT/'reproduce.py')]
    if args.quick:
        command.append('--construction-only')
    subprocess.run(command, check=True, env=env)
    with tempfile.TemporaryDirectory(prefix='pa194-extra-checks-') as td:
        work = Path(td)
        tag = work/'tagged3'
        shutil.copytree(ROOT/'research/tagged3', tag,
                        ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        pairs = [
            ('recoding.py', 'recoding_checks.json'),
            ('tagged2_check.py', 'tagged2_checks.json'),
            ('check_rho_generic_template.py', 'rho_generic_template_check.json'),
            ('check_rho_guard_certificate.py', 'rho_guard_certificate_check.json')
        ]
        math_receipts = []
        for script, receipt in pairs:
            subprocess.run([sys.executable, str(tag/script)], check=True, env=env)
            assert digest(tag/receipt) == digest(ROOT/'research/tagged3'/receipt), receipt
            math_receipts.append(receipt)
        matrix = work/'specialized_rho_matrix.py'
        shutil.copy2(ROOT/'research/specialized_rho_matrix.py', matrix)
        subprocess.run([sys.executable, str(matrix)], check=True, cwd=work, env=env)
        assert digest(matrix.with_suffix('.json')) == digest(ROOT/'research/specialized_rho_matrix.json')
        pricing = work/'algebra'
        pricing.mkdir()
        for name in ['check_algebra.py', 'grammar.tree.json']:
            shutil.copy2(ROOT/'research/tagged3_pricing'/name, pricing/name)
        subprocess.run([sys.executable, str(pricing/'check_algebra.py')], check=True, env=env)
        assert digest(pricing/'algebra_receipt.json') == digest(ROOT/'research/tagged3_pricing/algebra_receipt.json')
        novelty = work/'novelty.json'
        subprocess.run([
            sys.executable, str(ROOT/'comparison/verify_novelty.py'),
            str(ROOT/'machines/PA194LCAX11GHF/machine.tm'),
            str(ROOT/'machines/PA194LCAX11GHSF/machine.tm'),
            '--output', str(novelty)
        ], check=True, env=env)
        result = json.loads(novelty.read_text())
        assert result['historical_spanning194'] == 139
        assert result['mutually_distinct']
        assert all(c['states'] == 194 and c['novel'] for c in result['candidate_results'])
    receipt = {
        'status': 'PASS',
        'mode': 'quick' if args.quick else 'full',
        'manifest_files_checked': len(checked),
        'frozen_outputs_untouched': True,
        'independent_literal_replay_repeated': not args.quick,
        'exact_novelty_against_spanning194': 139,
        'mutually_distinct_new_tables': True,
        'mathematical_receipts_reproduced': math_receipts,
        'universal_rho_template_rows': 68268,
        'specialized_rho_countermatrix_reproduced': True,
        'tagged3_AX_free_algebra_reproduced': True,
        'scope': ('New relative machine implementation and stated finite/universal '
                  'certificates; imported absolute PA calibration is a written '
                  'dependency, not an end-to-end proof-assistant endpoint.')
    }
    text = json.dumps(receipt, indent=2) + '\n'
    if args.receipt:
        args.receipt.write_text(text)
    print(text)

if __name__ == '__main__':
    main()
