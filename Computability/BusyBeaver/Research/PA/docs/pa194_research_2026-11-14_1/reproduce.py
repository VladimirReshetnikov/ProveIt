#!/usr/bin/env python3
"""Fast offline reproduction of the delivered finite claims; no long searches."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
NAMES = ('PA194GD_SF', 'PA194GDH_SF', 'PA194GDHS_SF')


def check_manifest():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    if manifest['algorithm'] != 'sha256':
        raise ValueError('Unexpected manifest algorithm')
    for name, expected in manifest['files'].items():
        rel = PurePosixPath(name)
        if rel.is_absolute() or '..' in rel.parts:
            raise ValueError(f'Invalid manifest path: {name}')
        actual = hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f'Manifest mismatch: {name}')
    return len(manifest['files'])


def run(*args):
    completed = subprocess.run([sys.executable, '-B', *map(str, args)],
                               cwd=ROOT, check=True, capture_output=True, text=True)
    return completed.stdout


def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Verification requires assertions; run without -O.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Optional receipt outside the package')
    args = parser.parse_args()
    if args.output is not None and (args.output.resolve() == ROOT or ROOT in args.output.resolve().parents):
        parser.error('Choose an output path outside the frozen package')
    count = check_manifest()
    print(f'PASS: {count} manifest file hashes', flush=True)
    with tempfile.TemporaryDirectory(prefix='pa194-reproduction-') as temporary:
        temp = Path(temporary)
        rebuild = run(ROOT / 'verify.py', '--output', temp / 'machines')
        artifacts = 0
        for name in NAMES:
            expected = ROOT / 'machines' / name
            actual = temp / 'machines' / name
            assert {p.name for p in expected.iterdir()} == {p.name for p in actual.iterdir()}
            for path in expected.iterdir():
                assert path.read_bytes() == (actual / path.name).read_bytes(), str(path)
                artifacts += 1
        print('PASS: all three tables, local cases and whole-startup synchronizations', flush=True)
        independent_path = temp / 'independent.json'
        run(ROOT / 'verification/independent_variant_review.py', '--output', independent_path)
        independent = json.loads(independent_path.read_text())
        assert independent['status'] == 'PASS'
        print('PASS: independent literal verification', flush=True)
        modal = json.loads(run(ROOT / 'research/modal_consequents/reproduce.py'))
        assert modal['status'] == 'PASS'
        print('PASS: six Hilbert certificates, emitter inputs and recorded search identities', flush=True)
        novelty_path = temp / 'novelty.json'
        table_paths = [Path('machines') / name / 'machine.tm' for name in NAMES]
        run(ROOT / 'comparison/check_novelty.py', *table_paths, '--output', novelty_path)
        novelty = json.loads(novelty_path.read_text())
        frozen = json.loads((ROOT / 'comparison/new_machines_novelty.json').read_text())
        assert novelty == frozen, 'Novelty witnesses differ from the frozen result'
        assert all(not r['known_matches'] and r['prior_comparisons'] == 524 for r in novelty['results'])
        assert all(not r['same_graph'] for r in novelty['mutual_comparisons'])
        print('PASS: exact 524-representative novelty screen and pairwise distinctions', flush=True)
        assert check_manifest() == count
        result = {'status': 'PASS', 'commit': novelty['pinned_revision'],
                  'manifest_files_checked': count,
                  'generated_machine_files_identical': artifacts,
                  'machines': list(NAMES), 'rebuild': rebuild.splitlines(),
                  'independent_local_review': independent['status'],
                  'logical_certificate_checks': modal['certificate_checks'],
                  'novelty_representatives_per_machine': 524,
                  'all_pairwise_distinct': True,
                  'package_unchanged': True, 'long_searches_rerun': False,
                  'absolute_calibration': 'Imported written GD / revised AX11H dependency; no new end-to-end Lean proof.',
                  'scope': 'Finite table, local-proof, logical-template, provenance and novelty checks. Written iPRA induction is in the report.'}
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
