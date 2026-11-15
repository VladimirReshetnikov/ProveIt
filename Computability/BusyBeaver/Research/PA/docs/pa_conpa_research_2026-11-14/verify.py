#!/usr/bin/env python3
"""Offline replay for the two new PA194AX11GH/GHS machines.

Python 3.10+, standard library, no repository checkout or network required.
Full mode reconstructs and replays the literal symbolic certificates.  Quick
mode explicitly skips those two expensive layers.  Neither mode is a new
proof-assistant verification of the inherited mathematical PA calibration.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time
import zipfile

ROOT = Path(__file__).resolve().parent
FAMILIES = ('PA194AX11GH', 'PA194AX11GHS')

def require(condition, description):
    if not condition:
        raise RuntimeError(description)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Run without -O or PYTHONOPTIMIZE.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true',
                        help='Skip construction and independent symbolic runtime replay.')
    parser.add_argument('--skip-baseline', action='store_true',
                        help='Skip the retained baseline packet quick replay; recorded explicitly.')
    parser.add_argument('--output', type=Path,
                        help='New directory for outputs/logs; defaults to a temporary directory.')
    args = parser.parse_args()
    out = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='pa-conpa-replay-'))
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    expected = json.loads((ROOT / 'expected.json').read_text())
    result = dict(mode='quick' if args.quick else 'full', status='RUNNING',
                  python=sys.version.split()[0], machines={}, commands=[],
                  kernel_checked=False, arithmetic_derivation_checked_by_this_script=False)

    def run(label, script, *arguments):
        command = [sys.executable, '-B', str(script), *map(str, arguments)]
        print(label, flush=True)
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        begin = time.monotonic()
        with (out / (label + '.log')).open('w') as log:
            completed = subprocess.run(command, cwd=out, env=env,
                                       stdout=log, stderr=subprocess.STDOUT)
        result['commands'].append(dict(label=label, returncode=completed.returncode,
                                       seconds=round(time.monotonic()-begin, 3)))
        require(completed.returncode == 0, f'{label} failed; inspect {out / (label + ".log")}')

    manifest = ROOT / 'SHA256SUMS'
    if manifest.exists():
        count = 0
        for line in manifest.read_text().splitlines():
            h, name = line.split('  ', 1)
            require(digest(ROOT / name) == h, f'Integrity mismatch: {name}')
            count += 1
        result['manifest'] = dict(present=True, files_checked=count)
    else:
        result['manifest'] = dict(present=False)

    core = ('machine.tm', 'machine.native.tm', 'raw.native.tm', 'labels.json',
            'nodes.json', 'grammar.tree.json', 'folds.json', 'fold_cases.json',
            'sites.json', 'instructions.json')
    for family in FAMILIES:
        original = ROOT / 'machines' / family
        target = out / 'constructed' / family
        extra = ['--quick'] if args.quick else []
        run('construct_' + family, ROOT / 'construction/build.py',
            '--family', family, '--output', target, *extra)
        for name in core:
            require((original / name).read_bytes() == (target / name).read_bytes(),
                    f'Construction bytes differ: {family}/{name}')
        require(digest(original / 'machine.tm') == expected[family]['dense_sha256'],
                'Dense identity changed')
        run('commands_' + family, ROOT / 'verification/check_commands.py',
            '--machine', original, '--output', out / (family + '_commands.json'))
        run('source_' + family, ROOT / 'verification/check_source_commands.py',
            '--machine', original, '--output', out / (family + '_source'))
        command = json.loads((out / (family + '_commands.json')).read_text())
        source = json.loads((out / (family + '_source') / 'receipt.json').read_text())
        require(command['status'] == source['status'] == 'PASS', 'Source/command failure')
        result['machines'][family] = dict(
            dense_sha256=expected[family]['dense_sha256'],
            byte_identical_reconstruction=True, compared_construction_files=len(core),
            construction_contracts_replayed=not args.quick,
            command_words_replayed=True, source_command_binding_replayed=True,
            startup_steps=expected[family]['startup_steps'])

    if not args.quick:
        run('independent_literal', ROOT / 'verification/check_literal.py',
            *(ROOT / 'machines' / f for f in FAMILIES), '--output', out / 'independent')
        for family in FAMILIES:
            for name in ('contracts.json', 'list_lemmas.json', 'startup.json', 'receipt.json'):
                require((out / 'independent' / family / name).read_bytes() ==
                        (ROOT / 'machines' / family / 'independent' / name).read_bytes(),
                        f'Independent replay differs: {family}/{name}')
            result['machines'][family]['independent_literal_contracts_replayed'] = True
    else:
        for family in FAMILIES:
            result['machines'][family]['independent_literal_contracts_replayed'] = False

    run('physical_audit', ROOT / 'verification/physical_ipra_audit.py',
        '--bundle', ROOT, '--output', out / 'physical_audit.json')
    result['physical_frame_and_duration_audit_replayed'] = True
    run('novelty', ROOT / 'comparison/check_novelty.py', '--receipt', out / 'novelty.json')
    novelty = json.loads((out / 'novelty.json').read_text())
    require(novelty['historical_classes'] == 111 and novelty['historical_spanning'] == 110,
            'Unexpected comparison universe')
    require(all(r['historical_match_count'] == 0 for r in novelty['candidates']),
            'Historical novelty collision')
    require(all(not r['equal'] for r in novelty['candidate_pair_equalities']),
            'Candidates are equivalent')
    result['novelty'] = dict(historical_classes=111, historical_spanning=110,
                            candidate_matches=[0, 0], candidates_different=True,
                            full_tuple_comparisons=True)

    baseline = ROOT / 'references/pa194_ax11h_research_2026-11-14.zip'
    require(digest(baseline) == '93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075',
            'Wrong inherited written-proof baseline archive')
    result['baseline_archive_sha256'] = digest(baseline)
    if not args.skip_baseline:
        unpack = out / 'baseline'
        unpack.mkdir(exist_ok=True)
        with zipfile.ZipFile(baseline) as archive:
            for entry in archive.infolist():
                path = (unpack / entry.filename).resolve()
                require(path == unpack or unpack in path.parents, 'Unsafe archive member')
            archive.extractall(unpack)
        scripts = list(unpack.rglob('verify_all.py'))
        require(len(scripts) == 1, 'Ambiguous baseline verifier')
        run('baseline_quick', scripts[0], '--quick', '--output', out / 'baseline_replay')
        baseline_result = json.loads((out / 'baseline_replay/summary.json').read_text())
        require(baseline_result['status'] == 'PASS', 'Baseline finite binding failure')
        result['baseline_quick_replay'] = baseline_result
    else:
        result['baseline_quick_replay'] = 'SKIPPED BY REQUEST'
    result['status'] = 'PASS'
    result['elapsed_seconds'] = round(time.monotonic()-started, 3)
    (out / 'summary.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)
    print(f'Replay evidence: {out}', flush=True)

if __name__ == '__main__':
    main()
