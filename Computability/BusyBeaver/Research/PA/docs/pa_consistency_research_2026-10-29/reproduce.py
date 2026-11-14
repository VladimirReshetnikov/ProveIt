#!/usr/bin/env python3
"""Offline replay of the deliverable's comparison, source, and context claims.

No successful sub-208 machine is asserted by this packet. Optional full
baseline verification reuses the explicitly pinned upstream interpreter.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('reproduction-results'))
    parser.add_argument('--full-baseline', action='store_true')
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text())
    for relative, expected in manifest['files'].items():
        p = ROOT / relative
        need(p.is_file() and sha(p) == expected, f'Manifest mismatch: {relative}')
    commands = []

    def run(name, command, cwd=None):
        began = time.monotonic()
        proc = subprocess.run([str(x) for x in command], cwd=cwd or ROOT,
                              text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT)
        (out / (name + '.log')).write_text(proc.stdout)
        row = {'check': name, 'returncode': proc.returncode,
               'seconds': round(time.monotonic()-began, 4),
               'log': name + '.log'}
        commands.append(row)
        need(proc.returncode == 0, f'{name} failed; inspect {out / row["log"]}')
        print(name + ': PASS', flush=True)

    py = [sys.executable, '-B']
    run('table_comparison', py + [ROOT/'audit/compare_tables.py',
                                 '--output', out/'table_comparison.json'])
    t = json.loads((out/'table_comparison.json').read_text())
    need(t['class_count'] == 2 and len(t['tables']) == 9, 'Wrong graph classification')
    need(all(x['states'] == 208 and x['rows'] == 416 for x in t['tables']),
         'Wrong literal table census')
    run('source_comparison', py + [ROOT/'audit/compare_sources.py',
                                  '--output', out/'source_comparison.json'])
    run('source_specialization', py + [ROOT/'source_optimization/verify_source_optimization.py',
                                      '--output', out/'source'])
    run('source_specialization_optimized', py + ['-O', ROOT/'source_optimization/verify_source_optimization.py',
                                                '--output', out/'source_O'])
    normal = {p.relative_to(out/'source').as_posix(): sha(p)
              for p in (out/'source').rglob('*') if p.is_file()}
    optimized = {p.relative_to(out/'source_O').as_posix(): sha(p)
                 for p in (out/'source_O').rglob('*') if p.is_file()}
    need(normal == optimized, 'Normal and optimized Python outputs differ')
    expected = json.loads((ROOT/'source_optimization/verification_receipt.json').read_text())
    need(normal == expected['generated_files'], 'Source reproduction differs from delivered artifacts')
    run('context_certificate_and_scanner', py + [ROOT/'context_research/reproduce.py',
                                               '--output', out/'context'])
    # Keep the shipped negative-experiment files immutable during replay.
    rotation = out/'rotation_replay'
    rotation.mkdir(exist_ok=True)
    for name in ('replay_counterexamples.py', 'rejected207.native.tm', 'sites.json'):
        shutil.copy2(ROOT/'rotation_repair'/name, rotation/name)
    run('bounded_rotation_failures', py + [rotation/'replay_counterexamples.py'])
    negative = json.loads((rotation/'counterexamples.json').read_text())
    need(negative['status'] == 'REJECTED_FINITE_REPLAY', 'Wrong negative-experiment status')
    full = None
    if args.full_baseline:
        need(__debug__ and not sys.flags.optimize,
             'Full symbolic engine requires Python assertions enabled')
        target = out/'reference'
        target.mkdir(exist_ok=True)
        with zipfile.ZipFile(ROOT/'references/u208_research_2026-10-29.zip') as archive:
            for item in archive.infolist():
                rel = Path(item.filename)
                need(not rel.is_absolute() and '..' not in rel.parts,
                     'Unsafe reference archive member')
            archive.extractall(target)
        baseline = target/'u208_research_2026-10-29'
        run('full_symbolic_baseline', py + [baseline/'verify.py', '--full',
                                         '--output', out/'full_baseline.json'], cwd=baseline)
        full = json.loads((out/'full_baseline.json').read_text())
        need(full['status'] == 'PASS', 'Full baseline did not pass')
        for value in (full['runtime'], full['secondary']['runtime']):
            need(value['status'] == 'PASS' and value['contracts'] == 5084
                 and value['covered_rows'] == 416, 'Incomplete full baseline coverage')
    receipt = {
        'status': 'PASS', 'manifest_files_checked': len(manifest['files']),
        'graph_classes': 2, 'comparison_tables': 9,
        'source_specialization': json.loads((out/'source/result.json').read_text()),
        'normal_and_optimized_python_outputs_identical': True,
        'full_baseline_replayed': args.full_baseline,
        'full_baseline_runtime': None if full is None else
            {'B': full['runtime'], 'A': full['secondary']['runtime']},
        'commands': commands, 'seconds': round(time.monotonic()-started, 4),
        'smaller_literal_machine_claim': False,
        'claim_scope': 'Audited 208-state baselines, verified source specialization, '
                       'finite abstract invariant, and explicitly bounded rejected experiments.'
    }
    (out/'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({'status': 'PASS', 'seconds': receipt['seconds'],
                      'receipt': str(out/'receipt.json'),
                      'smaller_literal_machine_claim': False}, indent=2))


if __name__ == '__main__':
    main()
