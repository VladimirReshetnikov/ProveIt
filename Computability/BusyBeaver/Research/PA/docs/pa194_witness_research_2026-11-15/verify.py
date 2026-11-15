#!/usr/bin/env python3
"""Reproduce the two new machines' finite evidence without network access.

The retained mathematical iPRA arguments are separate from these finite checks.
Python 3.10+, standard library; run with assertions enabled.  Output goes only
to a fresh work directory, never into the sealed inputs.
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
import time

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'PA194H5X': {
        'dense': 'caffdd9f10d87d0d050eff07ab8f6e8edd9ab443aa94c948f03ee5316e37b614',
        'native': 'f45696ad9e78599bcc469d887c6295a4dc4afa00ff90458e230c9ee3ad3966d3',
        'sites': 3677, 'outcomes': 4786, 'tokens': 189,
        'literal_steps': 1110171, 'suffix': '',
    },
    'PA194JH5X': {
        'dense': '70be32fe352ee0fb29581f1037948f429334cfc9c6bcaa813aba43c4efba0148',
        'native': '957fef85080849e88bba4e82732065a350d382d489a032ddbc03756e8ef0c5e1',
        'sites': 3683, 'outcomes': 4794, 'tokens': 188,
        'literal_steps': 1097281, 'suffix': '_JH5X',
    },
}
BASELINE = '93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def load(path):
    return json.loads(Path(path).read_text())


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--work', type=Path, help='Fresh, nonexistent output directory.')
    ap.add_argument('--rebuild', action='store_true', help='Also rebuild both frozen tables and replay construction contracts.')
    ap.add_argument('--integrity', action='store_true', help='Also check the final SHA256SUMS of the complete package.')
    args = ap.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run without Python optimization.')
    require(sys.version_info >= (3, 10), 'Python 3.10 or newer is required.')
    if args.work:
        work = args.work.resolve()
        work.mkdir(parents=True, exist_ok=False)
    else:
        work = Path(tempfile.mkdtemp(prefix='pa194-witness-')).resolve()
    (work / 'logs').mkdir()
    environment = os.environ.copy()
    environment['PYTHONOPTIMIZE'] = '0'
    environment['PYTHONDONTWRITEBYTECODE'] = '1'
    results = []

    def run(name, relative_script, *arguments):
        command = [sys.executable, '-B', str(ROOT / relative_script), *map(str, arguments)]
        print(name, flush=True)
        log = work / 'logs' / (name + '.log')
        before = time.monotonic()
        with log.open('w') as stream:
            status = subprocess.run(command, cwd=ROOT, env=environment,
                                    stdout=stream, stderr=subprocess.STDOUT)
        result = dict(check=name, script=relative_script, returncode=status.returncode,
                      seconds=round(time.monotonic() - before, 3), log=str(log))
        results.append(result)
        if status.returncode:
            print(log.read_text()[-10000:])
            raise RuntimeError(name + ' failed; see ' + str(log))

    if args.integrity:
        rows = (ROOT / 'SHA256SUMS').read_text().splitlines()
        for row in rows:
            digest, name = row.split('  ', 1)
            require(sha(ROOT / name) == digest, 'Package integrity mismatch: ' + name)
        results.append(dict(check='package_integrity', status='PASS', files=len(rows)))

    require(sha(ROOT / 'references/pa194_ax11h_research_2026-11-14.zip') == BASELINE,
            'The retained calibration archive does not have the stated identity.')
    machines = []
    for family, expected in EXPECTED.items():
        source = ROOT / 'machines' / family
        require(sha(source / 'machine.tm') == expected['dense'], 'Dense table identity: ' + family)
        require(sha(source / 'machine.native.tm') == expected['native'], 'Native table identity: ' + family)
        machine = work / 'machines' / family
        if args.rebuild:
            run(family + '_rebuild', 'construction/build_' + family + '.py', '--output', machine)
            compared = ['machine.tm', 'machine.native.tm', 'raw.native.tm', 'labels.json',
                        'nodes.json', 'grammar.tree.json', 'sites.json', 'instructions.json']
            for name in compared:
                require((machine / name).read_bytes() == (source / name).read_bytes(),
                        'Reconstruction mismatch: ' + family + '/' + name)
        else:
            shutil.copytree(source, machine)

        source_result = work / 'source' / family
        run(family + '_source', 'verification/source/check_source_commands.py',
            '--machine', machine, '--output', source_result)
        sr = load(source_result / 'receipt.json')
        require(sr['status'] == 'PASS' and sr['source_sites'] == expected['sites']
                and sr['macro_tokens'] == expected['tokens'], 'Source count mismatch.')
        run(family + '_commands', 'verification/source/check_commands.py',
            '--machine', machine, '--output', source_result / 'commands.json')
        require(load(source_result / 'commands.json')['status'] == 'PASS', 'Command check failed.')

        suffix = expected['suffix']
        run(family + '_literal', 'verification/check_literal' + suffix + '.py',
            machine, '--output', work / 'literal')
        literal = work / 'literal' / family
        receipt = load(literal / 'receipt.json')
        require(receipt['status'] == 'PASS'
                and receipt['source_outcomes'] == expected['outcomes']
                and receipt['symbolic_steps'] == expected['literal_steps']
                and receipt['startup_steps'] == 57922, 'Literal receipt mismatch.')
        require((literal / 'contracts.json').read_bytes() ==
                (source / 'independent/contracts.json').read_bytes(), 'Literal contract bytes changed.')
        shutil.copytree(literal, machine / 'independent', dirs_exist_ok=True)
        run(family + '_closure', 'verification/physical_ipra_audit' + suffix + '.py',
            '--machine', machine, '--output', work / (family + '_closure.json'))
        require(load(work / (family + '_closure.json'))['status'] == 'PASS', 'Frame closure failed.')
        machines.append(receipt)

    run('witness_logical_templates', 'logic/verify_logic.py', ROOT / 'logic/certificates',
        '--output', work / 'logic.json')
    run('join_logical_templates', 'logic/verify_j.py', ROOT / 'logic/j_certificates',
        '--output', work / 'logic_J.json')
    run('generalized_join_templates', 'logic/verify_ja.py', ROOT / 'logic/ja_certificates',
        '--output', work / 'logic_JA.json')
    run('retained_premise_exchange', 'verification/exchange_certificate.py')
    run('structural_novelty', 'comparison/check_novelty.py',
        *(ROOT / 'machines' / f / 'machine.tm' for f in EXPECTED),
        '--output', work / 'novelty.json')
    novelty = load(work / 'novelty.json')
    require(novelty['reference_count'] == 139, 'Wrong pinned frontier size.')
    require(all(r['new_structural_class'] for r in novelty['candidates']), 'Novelty failed.')
    run('comparison_packet', 'comparison/verify_packet.py', '--output', work / 'comparison.json')

    record = dict(status='PASS', pinned_repository='8d31445d858761a8f6150c2e5012adae8895e932',
                  baseline_archive_sha256=BASELINE, reconstruction_requested=args.rebuild,
                  machine_receipts=machines, checks=results,
                  kernel_checked=False,
                  scope='Finite reconstruction, universal schematic contract replay and proof-template checking. '
                        'The written iPRA interpretation and retained PA calibration are separate mathematical arguments.')
    (work / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(dict(status='PASS', output=str(work), machines=list(EXPECTED),
                          checks=len(results), kernel_checked=False), indent=2), flush=True)


if __name__ == '__main__':
    main()
