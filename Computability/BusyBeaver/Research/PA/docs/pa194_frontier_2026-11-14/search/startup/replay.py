#!/usr/bin/env python3
"""Replay startup detector controls; optionally rerun all three bounded searches."""
import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import tempfile

HERE = pathlib.Path(__file__).resolve().parent


def totals(path):
    lines = path.read_text().splitlines()
    line = next((line for line in reversed(lines) if line.startswith('DONE ')), None)
    if line is None:
        raise ValueError(f'No DONE totals in {path}')
    items = line.split()[1:]
    result = dict(zip(items[::2], items[1::2]))
    return {key: int(value) for key, value in result.items() if key != 'seconds'}


def run(args, stdout, stderr):
    with stdout.open('w') as out, stderr.open('w') as err:
        subprocess.run([str(arg) for arg in args], check=True, stdout=out, stderr=err)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full', action='store_true', help='Rerun all three 200,000-step searches too.')
    parser.add_argument('--output', type=pathlib.Path)
    parser.add_argument('--compiler', default='g++')
    args = parser.parse_args()
    out = (args.output or pathlib.Path(tempfile.mkdtemp(prefix='pa-startup-'))).resolve()
    if out == HERE or HERE in out.parents:
        raise ValueError('Use an output directory outside the frozen startup package.')
    out.mkdir(parents=True, exist_ok=True)
    provenance = json.loads((HERE / 'PROVENANCE.json').read_text())
    checked = []
    for name, expected in provenance['replay_input_sha256'].items():
        actual = hashlib.sha256((HERE / name).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f'Input hash mismatch: {name}')
        checked.append(name)
    summary = json.loads((HERE / 'summary.json').read_text())
    for item in summary['experiments']:
        actual = totals(HERE / item['log'])
        if actual != item['integer_totals']:
            raise ValueError(f'Recorded totals mismatch: {item["name"]}')
        if (HERE / item['output']).read_text():
            raise ValueError(f'Expected zero hits, found output: {item["output"]}')
    controls = []
    for name, define, expected_name in [
        ('detector_selftest', None, 'detector_selftest.log'),
        ('detector_selftest_old', '-DORIGINAL_DETECTOR', 'detector_selftest_old.log'),
    ]:
        compiler_args = [args.compiler, '-O3', '-std=c++17']
        if define:
            compiler_args.append(define)
        compiler_args += [HERE / 'detector_selftest.cpp', '-o', out / name]
        run(compiler_args, out / f'{name}.build.out', out / f'{name}.build.log')
        run([out / name, HERE / 'primary194.native.tm'], out / f'{name}.log', out / f'{name}.stderr')
        if (out / f'{name}.log').read_bytes() != (HERE / expected_name).read_bytes():
            raise ValueError(f'Positive control output differs: {name}')
        controls.append(name)
    rerun = []
    if args.full:
        for source in ('quad_allframes', 'quad_firstwrite'):
            run([args.compiler, '-O3', '-std=c++17', HERE / f'{source}.cpp', '-o', out / source],
                out / f'{source}.build.out', out / f'{source}.build.log')
        for item in summary['experiments']:
            run([out / item['executable'], HERE / item['input_table'], HERE / 'safe_edits.tsv',
                 HERE / 'all_source_templates.tsv', item['stage'], 200000],
                out / item['output'], out / item['log'])
            actual = totals(out / item['log'])
            if actual != item['integer_totals'] or (out / item['output']).read_text():
                raise ValueError(f'Full replay differs: {item["name"]}')
            rerun.append(item['name'])
    result = {'status': 'PASS', 'input_hashes_checked': checked,
              'recorded_totals_checked': [item['name'] for item in summary['experiments']],
              'positive_controls_replayed': controls, 'searches_replayed': rerun,
              'full_replay': args.full, 'output_directory': str(out)}
    (out / 'receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
