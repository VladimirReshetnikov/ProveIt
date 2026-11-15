#!/usr/bin/env python3
"""Rebuild five new 194-state machines and verify their exact finite evidence.

Default: isolated reconstruction, recorded-certificate bindings, finite source,
startup and clock audits, and full-tuple novelty against 110 prior graphs.
--physical also regenerates every local physical contract for both parents
and all five new machines. Neither mode checks an arithmetic derivation or
runs a proof-assistant kernel. All newly written evidence stays outside the
frozen release, in --out or a freshly created temporary directory.
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
NAMES = ['PA194LC', 'PA194LC_A', 'PA194LC_B', 'PA194LC_C']
LH = ROOT / 'additional/PA194LC_AX11H'
CALIBRATION_SHA = '93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*args):
    print('+', sys.executable, '-B', *map(str, args), flush=True)
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    subprocess.run([sys.executable, '-B', *map(str, args)], cwd=ROOT,
                   env=env, check=True)


def bind(table_dir, evidence_dir, outcomes):
    certificate = json.loads((evidence_dir / 'receipt.json').read_text())
    assert certificate['status'] == 'PASS'
    assert certificate['dense_sha256'] == sha(table_dir / 'machine.tm')
    assert certificate['native_sha256'] == sha(table_dir / 'machine.native.tm')
    assert certificate['contracts_sha256'] == sha(evidence_dir / 'contracts.json')
    assert certificate['states'] == 194 and certificate['rows'] == 388
    assert certificate['source_outcomes'] == outcomes
    assert certificate['list_lemmas_from_literal_table'] == 4
    assert not certificate['box_oracles']
    assert certificate['whole_blank_startup']
    assert certificate['independent_source_resolvers_agree']
    assert certificate['minimum_positive_duration_constant'] >= 3
    return dict(directory=str(table_dir.relative_to(ROOT)),
                dense_sha256=certificate['dense_sha256'],
                native_sha256=certificate['native_sha256'],
                contracts_sha256=certificate['contracts_sha256'])


def main():
    assert __debug__ and not sys.flags.optimize, 'Run without Python -O.'
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--physical', action='store_true')
    ap.add_argument('--out', type=Path)
    args = ap.parse_args()
    out = (args.out or Path(tempfile.mkdtemp(prefix='pa194-release-replay-'))).resolve()
    if out == ROOT or ROOT in out.parents:
        ap.error('--out must be outside the frozen release directory.')
    out.mkdir(parents=True, exist_ok=True)
    print('Evidence directory:', out, flush=True)

    with tempfile.TemporaryDirectory(prefix='pa194lc-rebuild-') as temp:
        temp = Path(temp)
        run('construction/build.py', '--output', temp)
        for name in NAMES:
            for path in (temp / name).iterdir():
                assert path.read_bytes() == (ROOT / 'machines' / name / path.name).read_bytes(), (name, path.name)

    directories = [Path('reference/primary')] + [Path('machines') / n for n in NAMES]
    bindings = [bind(ROOT / d, ROOT / d / 'independent', 4780) for d in directories]
    if args.physical:
        with tempfile.TemporaryDirectory(prefix='pa194lc-physical-') as temp:
            temp = Path(temp)
            copies = []
            for directory in directories:
                # The frozen primary receipt was originally generated under
                # the directory name "baseline"; check.py records path.name.
                # Preserve that provenance label for byte-identical receipts.
                copied = (temp / 'reference/baseline' if directory == Path('reference/primary')
                          else temp / directory)
                shutil.copytree(ROOT / directory, copied)
                copies.append(copied)
            run('verification/check.py', *copies)
            for directory, copied in zip(directories, copies):
                for name in ['contracts.json', 'list_lemmas.json', 'receipt.json']:
                    assert (copied / 'independent' / name).read_bytes() == (ROOT / directory / 'independent' / name).read_bytes(), (str(directory), name)
                destination = out / 'physical' / directory
                destination.mkdir(parents=True, exist_ok=True)
                for name in ['contracts.json', 'list_lemmas.json', 'receipt.json']:
                    shutil.copy2(copied / 'independent' / name, destination / name)

    run('verification/check_source_binding.py', '--out', out / 'source_binding.json')
    run('verification/check_startup.py', *directories, '--out', out / 'startup.json')
    run('verification/check_duration_bounds.py',
        *[d / 'independent/contracts.json' for d in directories],
        '--out', out / 'duration_bounds.json')
    run('verification/check_iteration_cost.py', '--out', out / 'iteration_cost.json')

    bindings += [bind(LH, LH / 'independent/results/PA194LC_AX11H', 4778),
                 bind(LH / 'parent', LH / 'independent/results/PA194AX11H', 4778)]
    lh_args = [LH / 'verify_all.py', '--output', out / 'lc_ax11h']
    if not args.physical:
        lh_args.append('--quick')
    run(*lh_args)
    # Reaudit the frozen affine coefficients even in the default mode. This
    # is explicitly distinct from regenerating physical symbolic contracts.
    run(LH / 'check_durations.py', '--evidence', LH / 'independent/results',
        '--output', out / 'lc_ax11h_recorded_duration_bounds.json')
    if args.physical:
        for family in ['PA194AX11H', 'PA194LC_AX11H']:
            for name in ['contracts.json', 'list_lemmas.json', 'receipt.json']:
                assert (out / 'lc_ax11h/independent' / family / name).read_bytes() == (LH / 'independent/results' / family / name).read_bytes(), (family, name)

    # Require every final candidate to be present, then independently replay
    # canonical tuples from the hash-pinned frozen comparison copies.
    candidates = json.loads((ROOT / 'late_snapshot/candidate_manifest.json').read_text())
    for item in candidates:
        path = ROOT / item['release_path_if_present']
        assert path.is_file() and sha(path) == item['sha256'], item['name']
        assert path.read_bytes() == (ROOT / 'late_snapshot' / item['path']).read_bytes()
    run('late_snapshot/check_novelty.py', '--out', out / 'novelty.json')
    assert sha(ROOT / 'reference/ax11h_calibration_603c58c.zip') == CALIBRATION_SHA

    summary = dict(status='PASS', rebuilt_new_machines=5,
        rebuilt_artifacts_equal=True,
        physical_contracts_regenerated=args.physical,
        recorded_duration_coefficients_reaudited=True,
        certificate_bindings=bindings,
        reference_194_graphs=110, new_graphs=5,
        concurrent_gax11_duplicate_expected=True,
        imported_ax11h_archive_sha256=CALIBRATION_SHA,
        arithmetic_derivation_checked_by_this_script=False,
        absolute_result='Written LC_AX11H corollary in the report imports the separate revised AX11H calibration theorem.',
        new_lean_endpoint=False,
        scope='Exact finite reconstruction and certificate replay; written relative iPRA proofs and the imported absolute corollary are in the report.',
        output_directory=str(out))
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
