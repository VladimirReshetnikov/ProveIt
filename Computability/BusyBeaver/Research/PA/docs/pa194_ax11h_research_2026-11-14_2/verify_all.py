#!/usr/bin/env python3
"""Rebuild and verify the delivered 194-state alternatives.

Default: construction contracts plus independent literal contracts for both
machines. --quick explicitly omits those expensive replays, checks their
stored bindings, and still reconstructs tables and replays command/novelty
checks. These scripts check the finite implementation certificates. The written
arithmetic proof in report/main.pdf is not verified by this script.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
FAMILIES = ('PA194AX11H', 'PA194QAX11H')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def run(arguments, log):
    with log.open('w') as stream:
        p = subprocess.run([sys.executable, '-B', *map(str, arguments)],
                           cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    if p.returncode:
        print(log.read_text()[-10000:], file=sys.stderr)
        raise RuntimeError(f'Failed command; complete log: {log}')


def check_manifest():
    path = ROOT / 'SHA256SUMS'
    if not path.exists():
        return {'present': False, 'note': 'Development tree; release includes SHA256SUMS.'}
    total = 0
    for line in path.read_text().splitlines():
        expected, name = line.split('  ', 1)
        p = ROOT / name
        assert p.is_file() and sha(p) == expected, name
        total += 1
    return {'present': True, 'files_checked': total}


def main():
    assert __debug__ and not sys.flags.optimize, 'Run without Python -O.'
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quick', action='store_true')
    p.add_argument('--output', type=Path, help='New replay directory; defaults to a temporary directory.')
    args = p.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='pa194-replay-'))
    out.mkdir(parents=True, exist_ok=True)
    assert out != ROOT and ROOT not in out.parents, 'Keep replay output outside the release tree.'
    result = {'mode': 'quick' if args.quick else 'full', 'output': str(out),
              'manifest': check_manifest(), 'machines': {},
              'kernel_checked': False, 'arithmetic_derivation_checked_by_this_script': False}
    expected = read(ROOT / 'expected.json')
    print('Checking all physical-frame endpoints and primitive recursive duration vectors', flush=True)
    run(['verification/physical_ipra_audit.py', '--bundle', ROOT,
         '--output', out / 'physical_ipra_audit.json'], out / 'physical_ipra_audit.log')
    assert read(out / 'physical_ipra_audit.json') == read(ROOT / 'verification/physical_ipra_audit_receipt.json')
    result['physical_frame_and_duration_audit_replayed'] = True
    print('Checking pinned source identities and finite logical adapters', flush=True)
    run(['verification/check_reference_sources.py', '--output', out / 'source_reference_audit.json'],
        out / 'source_reference_audit.log')
    assert read(out / 'source_reference_audit.json') == read(ROOT / 'verification/source_reference_audit.json')
    result['saved_source_identities_replayed'] = True
    foundation = ROOT / 'research/foundation_calibration'
    run([foundation / 'check_closure_constructors.py', '--output', out / 'closure_receipt.json'],
        out / 'foundation_closure.log')
    assert read(out / 'closure_receipt.json') == read(foundation / 'closure_receipt.json')
    result['finite_foundation_proof_constructors_replayed'] = True
    endpoint = out / 'foundation_endpoint'
    shutil.copytree(foundation / 'current_endpoint', endpoint)
    run([endpoint / 'compare_endpoint.py'], out / 'foundation_endpoint.log')
    comparison = read(endpoint / 'comparison_receipt.json')
    assert comparison['shared_equation_checks'] == 119 and comparison['unequal_checks'] == []
    assert comparison == read(foundation / 'current_endpoint/comparison_receipt.json')
    result['current_foundation_equation_comparisons'] = 119
    exchange = out / 'exchange'
    shutil.copytree(ROOT / 'references/q_exchange', exchange)
    run([exchange / 'exchange_certificate.py'], out / 'exchange.log')
    assert read(exchange / 'exchange_certificate.json') == read(ROOT / 'references/q_exchange/exchange_certificate.json')
    result['fixed_premise_exchange_replayed'] = True
    fingerprints = []
    for f in FAMILIES:
        print(f'{f}: reconstructing exact table', flush=True)
        delivered = ROOT / 'machines' / f
        replay = out / f
        command = ['build.py', '--family', f, '--output', replay]
        if args.quick:
            command.append('--quick')
        run(command, out / f'{f}_build.log')
        for name in ('machine.tm', 'machine.native.tm', 'raw.native.tm', 'labels.json',
                     'nodes.json', 'grammar.json', 'grammar.tree.json',
                     'sites.json', 'instructions.json', 'folds.json', 'local_folds.json'):
            assert (delivered / name).read_bytes() == (replay / name).read_bytes(), (f, name)
        assert sha(replay / 'machine.tm') == expected[f]['dense_sha256']
        run(['verification/check_commands.py', '--machine', replay,
             '--output', out / f'{f}_commands.json'], out / f'{f}_commands.log')
        assert read(out / f'{f}_commands.json') == read(delivered / 'command_certificate.json')
        print(f'{f}: binding every source instruction to arithmetic templates', flush=True)
        run(['verification/check_source_commands.py', '--machine', replay,
             '--output', replay / 'source_command'], out / f'{f}_source_command.log')
        for name in ('receipt.json', 'atom_ports.json', 'template_ports.json'):
            assert (replay / 'source_command' / name).read_bytes() == (delivered / 'source_command' / name).read_bytes(), (f, name)
        stored = read(delivered / 'independent/receipt.json')
        assert stored['status'] == 'PASS' and stored['source_contracts'] == 4778
        assert stored['source_sites'] == 3671 and stored['startup_steps'] == 57922
        assert stored['complete_startup_tape_equal'] and stored['dense_native_conjugacy']
        assert stored['arithmetic_box_oracles'] is False
        assert stored['dense_sha256'] == sha(delivered / 'machine.tm')
        assert stored['native_sha256'] == sha(delivered / 'machine.native.tm')
        assert stored['contracts_sha256'] == sha(delivered / 'independent/contracts.json')
        if not args.quick:
            print(f'{f}: replaying every independent literal source contract', flush=True)
            run(['verification/check_literal.py', '--machine', replay, '--output', replay / 'independent'],
                out / f'{f}_literal.log')
            for name in ('contracts.json', 'list_lemmas.json', 'receipt.json'):
                assert (replay / 'independent' / name).read_bytes() == (delivered / 'independent' / name).read_bytes(), (f, name)
        print(f'{f}: exact corpus novelty comparison', flush=True)
        novelty = out / f'{f}_novelty.json'
        run(['comparison/scanner/compare_novelty.py', replay / 'machine.tm',
             ROOT / 'comparison/census/frontier_tables', '--output', novelty], out / f'{f}_novelty.log')
        n = read(novelty)
        assert n['compared_classes'] == 82 and len(n['excluded_no_spanning_root']) == 2
        assert n['matches'] == [] and n['whole_table_spanning']
        old = read(ROOT / 'comparison' / f'novelty_{f}.json')
        assert n['candidate_cosmetic_fingerprint'] == old['candidate_cosmetic_fingerprint']
        fingerprints.append(n['candidate_cosmetic_fingerprint'])
        result['machines'][f] = {
            'dense_sha256': sha(replay / 'machine.tm'),
            'byte_identical_reconstruction': True, 'command_checks_replayed': True,
            'source_command_binding_replayed': True,
            'construction_contracts_replayed': not args.quick,
            'independent_literal_contracts_replayed': not args.quick,
            'stored_literal_certificate_bindings_checked': True,
            'novelty_comparisons': n['compared_classes'],
            'nonspanning_invariant_exclusions': 2, 'novelty_matches': []}
    assert fingerprints[0] != fingerprints[1]
    result['candidates_cosmetically_distinct_from_each_other'] = True
    result['status'] = 'PASS'
    (out / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
