#!/usr/bin/env python3
"""Offline reproduction of the K226 construction and mathematical checks.

Python 3.10+ and a C++17 compiler are required. --full reconstructs all
universally quantified instruction proofs. The separate rocq-extension
builder supplies the proof-assistant endpoint with its pinned toolchain.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def require(value, message):
    if not value:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_manifest(root):
    entries = json.loads((root / 'MANIFEST.json').read_text())['files']
    for name, digest in entries.items():
        require(sha(root / name) == digest, 'Manifest mismatch: ' + name)
    return len(entries)


def compare_json(a, b, ignore=()):
    x, y = json.loads(a.read_bytes()), json.loads(b.read_bytes())
    if ignore:
        x = {k: v for k, v in x.items() if k not in ignore}
        y = {k: v for k, v in y.items() if k not in ignore}
    require(x == y, 'Different evidence: ' + str(a) + ' and ' + str(b))


def evidence_audit():
    source = json.loads((ROOT / 'source/k226_sites.json').read_bytes())
    cases = json.loads((ROOT / 'evidence/runtime226/cases.json').read_bytes())
    expected = [(i, positive) for i, (_, op, _) in enumerate(source)
                for positive in ([False, True] if op == 'CD' else [False])]
    require([(c['site_index'], c['positive']) for c in cases] == expected,
            'Delivered runtime cases do not cover exactly all source guards')
    require(len(expected) == 6656, 'Wrong guard count')
    require(sum(c['symbolic_steps'] for c in cases) == 1615284,
            'Wrong symbolic-rule census')
    require(max(c['symbolic_steps'] for c in cases) == 412, 'Wrong largest case')
    compare_json(ROOT / 'evidence/runtime226/cases.json',
                 ROOT / 'evidence/portable_runtime226/cases.json')
    compare_json(ROOT / 'evidence/runtime226/verification.json',
                 ROOT / 'evidence/portable_runtime226/verification.json',
                 ignore=('seconds', 'checker_sha256'))
    return {'cases': len(cases), 'symbolic_rules': 1615284,
            'both_delivered_full_case_arrays_equal': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True,
                        help='New or empty work directory outside the delivered package')
    parser.add_argument('--full', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    require(out != ROOT and ROOT not in out.parents,
            'Choose an output directory outside the delivered package')
    require(not out.exists() or not any(out.iterdir()), 'Output directory must be new or empty')
    out.mkdir(parents=True, exist_ok=True)
    manifest_count = check_manifest(ROOT)
    print(f'manifest PASS ({manifest_count} files)', flush=True)
    py = sys.executable

    def run(name, command):
        result = subprocess.run(list(map(str, command)), text=True, capture_output=True,
                                env=dict(os.environ, PYTHONDONTWRITEBYTECODE="1"))
        (out / (name + '.log')).write_text(result.stdout + result.stderr)
        require(result.returncode == 0,
                name + ' failed; inspect ' + str(out / (name + '.log')) + '\n' +
                result.stdout[-1500:] + result.stderr[-1500:])
        print(name + ' PASS', flush=True)

    run('rocq_data_bindings', [py, '-B', ROOT / 'rocq-extension/build.py',
        '--reference', ROOT / 'vendor/k230-rocq',
        '--jeff-reference', ROOT / 'vendor/jeff-reference', '--check-only', '--all'])
    run('rocq_checked_source_correspondence',
        [py, '-B', ROOT / 'rocq-extension/receipts/check_source_correspondence.py'])
    run('independent_rocq_literal_bindings',
        [py, '-B', ROOT / 'verification/independent_source_dense_audit.py',
         '--rocq', ROOT / 'rocq-extension/coq/226',
         '--dense-table', ROOT / 'machines/k226.tm',
         '--sparse-table', ROOT / 'machines/k226_k230labels.tm',
         '--sites', ROOT / 'source/k226_sites.json', '--out', out / 'rocq_literal_bindings.json'])
    compare_json(out / 'rocq_literal_bindings.json',
                 ROOT / 'evidence/independent/independent_source_dense_receipt.json')

    # Source generators write beside themselves; use a disposable exact copy.
    source_copy = out / 'source-construction'
    shutil.copytree(ROOT / 'source-construction', source_copy)
    run('source_construction', [py, '-B', source_copy / 'reproduce.py'])
    for generated, selected in [
        ('generated226/02_k226/k226.tm', 'machines/k226.tm'),
        ('generated226/02_k226/sites.json', 'source/k226_sites.json'),
        ('generated/05_k227/k227.tm', 'machines/k227.tm')]:
        require((source_copy / generated).read_bytes() == (ROOT / selected).read_bytes(),
                'Construction output mismatch: ' + selected)
    run('independent_h_source', [py, '-B', ROOT / 'verification/independent_h_source.py',
        '--k230-sites', ROOT / 'source/k230_sites.json',
        '--h-sites', ROOT / 'source/h_sites.json', '--output', out / 'h_source.json'])
    compare_json(out / 'h_source.json', ROOT / 'evidence/independent/independent_h_source.json')
    run('independent_delayed_fold', [py, '-B', ROOT / 'verification/independent_fold229.py',
        '--old', ROOT / 'machines/k230.tm', '--new', ROOT / 'machines/k229_k230labels.tm',
        '--canonical', ROOT / 'machines/k229.tm', '--output', out / 'fold229.json'])
    compare_json(out / 'fold229.json', ROOT / 'evidence/independent/independent_fold229.json')
    run('native_construction_and_controls', [py, '-B', ROOT / 'native226_extension/reproduce.py',
        '--base', ROOT / 'native227_evidence', '--output', out / 'native226'])

    command = [py, '-B', ROOT / 'verification/verify_protocol.py',
        '--engine-dir', ROOT / 'verification/engine',
        '--table', ROOT / 'machines/k226_native.tm',
        '--sites', ROOT / 'source/k226_sites.json',
        '--reference', ROOT / 'source/h_sites.json',
        '--boot-reference', ROOT / 'verification/boot_reference.json',
        '--output', out / 'runtime226']
    if args.full:
        command.append('--full')
    run('selected_protocol', command)
    if args.full:
        compare_json(out / 'runtime226/cases.json', ROOT / 'evidence/portable_runtime226/cases.json')
        compare_json(out / 'runtime226/verification.json',
                     ROOT / 'evidence/portable_runtime226/verification.json', ignore=('seconds',))
    compare_json(out / 'runtime226/bootstrap.json', ROOT / 'evidence/portable_runtime226/bootstrap.json')
    run('constructor_fusion', [py, '-B', ROOT / 'formalisms/constructor_fusion/build_e679.py',
                              '--out', out / 'E679'])
    for name in ('E679.bits', 'E679.json', 'verification.json'):
        require((out / 'E679' / name).read_bytes() ==
                (ROOT / 'formalisms/constructor_fusion/generated' / name).read_bytes(),
                'Constructor packet mismatch: ' + name)
    for label, source in [('663', ROOT / 'formalisms/E663.json'),
                          ('679', ROOT / 'formalisms/constructor_fusion/generated/E679.json')]:
        run('prefix' + label, [py, '-B', ROOT / 'formalisms/prefix_codec.py',
                              '--input', source, '--out', out / ('prefix' + label)])
        for name in ('prefix.bits', 'decoded.json', 'verification.json'):
            require((out / ('prefix' + label) / name).read_bytes() ==
                    (ROOT / ('formalisms/prefix' + label) / name).read_bytes(),
                    'Prefix packet mismatch: ' + label + '/' + name)

    audit = evidence_audit()
    receipt = {'status': 'K226_PORTABLE_REPRODUCTION_PASS', 'full_symbolic_rebuild': args.full,
               'manifest_files': manifest_count, 'machine_sha256': sha(ROOT / 'machines/k226.tm'),
               'working_states': 226, 'transition_rows': 452,
               'fresh_source_and_local_proofs': True, 'fresh_exact_blank_initialization': True,
               'finite_instruction_fixtures': 26624, 'finite_fixture_transitions_including_boot': 15414531,
               'delivered_full_evidence_audit': audit, 'prefix_packet_bits': {'E663': 574, 'E679': 586},
               'rocq_scope': 'Separate rocq-extension/build.py; see its exact endpoint receipts.'}
    (out / 'verification.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run Python with assertions enabled')
    main()
