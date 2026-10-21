#!/usr/bin/env python3
"""Reproduce the supplemental root searches using only the containing archive.

Python 3 and a C++17 compiler are required. Discovery filters are finite and
their negative results are not lower bounds on equivalent Turing machines.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys

HERE = Path(__file__).resolve().parent
CODE = HERE / 'code'
KNOWN = {
    'baseline218/k218.native.tm': '2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f',
    'baseline218/sites218.json': 'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9',
    'core217/core.native.tm': 'c3d90a672481086329d8ed93da24a885d80a553ae6298b3a6444bea0fd5cee53',
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet-root', type=Path, default=HERE.parent,
                    help='directory containing baseline218/, core217/, machine-search/')
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--cxx', default=os.environ.get('CXX', 'g++'))
    ap.add_argument('--edits', type=Path,
                    help='edit catalog for initializer searches; default is the recorded 492 edits')
    ap.add_argument('task', choices=['smoke', 'check-rejected', 'complete', 'onespare', 'two-row',
                    'runtime-rewrites', 'single-initializers', 'paired-initializers', 'all'])
    a = ap.parse_args()
    root, out = a.packet_root.resolve(), a.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    build = out / 'build'
    build.mkdir(exist_ok=True)
    for name, expected in KNOWN.items():
        path = root / name
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise SystemExit(f'Input hash mismatch or missing file: {path}')
    sites = json.loads((root / 'baseline218/sites218.json').read_text())
    site_text = out / 'sites218.txt'
    site_text.write_text(''.join(f'{pc} {op} {arg if arg is not None else 0}\n'
                                for pc, op, arg in sites))
    commands = []

    def execute(argv, log):
        argv = list(map(str, argv))
        print('RUN', ' '.join(argv), flush=True)
        commands.append({'argv': argv, 'log': str(log.relative_to(out))})
        with log.open('w') as stream:
            p = subprocess.run(argv, stdout=stream, stderr=subprocess.STDOUT)
        if p.returncode:
            print(log.read_text()[-5000:], flush=True)
            raise SystemExit(f'Failed with exit {p.returncode}: {argv[0]}')
        tail = log.read_text().splitlines()[-2:]
        print('\n'.join(tail), flush=True)

    compiled = {}

    def cpp(stem):
        if stem not in compiled:
            target = build / stem
            execute([a.cxx, '-O3', '-std=c++17', CODE / f'{stem}.cpp', '-o', target],
                    out / f'compile-{stem}.log')
            compiled[stem] = target
        return compiled[stem]

    def contexts(stem, core=False):
        filename = 'core_contexts.txt' if core else (
            'onespare_contexts.txt' if stem == 'onespare_contexts' else 'runtime_contexts_complete.txt')
        path = out / filename
        table = root / ('core217/core.native.tm' if core else 'baseline218/k218.native.tm')
        execute([cpp(stem), table, site_text, path], out / f'{path.stem}.log')
        return path

    def python(stem, extra=()):
        execute([sys.executable, CODE / f'{stem}.py', '--packet-root', root,
                 '--output', out, *extra], out / f'{stem}.log')

    def initializer(stem, edits, all_starts):
        log = out / f'{stem}.log'
        execute([cpp(stem), root / 'core217/core.native.tm', edits, int(all_starts)], log)
        match = re.search(r'COMPLETE (\d+) frames (\d+) rays (\d+) limits (\d+) halts (\d+)',
                          log.read_text())
        if not match:
            raise SystemExit('Missing complete initializer census')
        record = dict(zip(['cases', 'frames', 'rays', 'limits', 'halts'], map(int, match.groups())))
        record.update({'status': 'FINITE_INITIALIZER_SEARCH',
                       'edit_catalog_sha256': hashlib.sha256(Path(edits).read_bytes()).hexdigest(),
                       'all_working_states_as_starts': all_starts,
                       'step_limit': 1500000,
                       'ray_meaning': 'Self-loop moving outward through previously blank cells; infinite continuation follows by induction.',
                       'limit_meaning': 'No conclusion: finite step or tape bound reached.'})
        (out / f'{stem}.json').write_text(json.dumps(record, indent=2) + '\n')

    def smoke():
        noop = out / 'baseline-noop-edit.txt'
        noop.write_text('0 0 1 1 94\n')
        log = out / 'baseline-positive-control.log'
        execute([cpp('rewrite_init_search'), root / 'baseline218/k218.native.tm', noop, 0], log)
        required = 'START 0 FRAME 312909 h -5 gap 80 logical 3 0 0 0 3 0 0 0 0 spares 130'
        if required not in log.read_text():
            raise SystemExit('Baseline clean-frame positive control failed')
        python('check_preliminary_failure')
        python('check_raw_frame')
        (out / 'smoke.json').write_text(json.dumps({
            'status': 'PASS', 'baseline_startup_steps': 312909,
            'baseline_startup_head': -5, 'baseline_spares': 130,
            'preliminary_false_fold_counterexample_reproduced': True,
            'raw_alternate_frame_counterexample_reproduced': True}, indent=2) + '\n')

    tasks = ['smoke', 'complete', 'onespare', 'two-row', 'runtime-rewrites',
             'single-initializers', 'paired-initializers'] if a.task == 'all' else [a.task]
    edits = a.edits.resolve() if a.edits else HERE / 'data/runtime_rewrites.txt'
    for task in tasks:
        if task == 'smoke':
            smoke()
        elif task == 'check-rejected':
            python('check_hits')
        elif task == 'complete':
            python('complete_search', ['--contexts', contexts('runtime_contexts')])
        elif task == 'onespare':
            python('onespare_search', ['--contexts', contexts('onespare_contexts')])
        elif task == 'two-row':
            domain = out / 'discovery_domain9_complete.json'
            if not domain.exists():
                python('complete_search', ['--contexts', contexts('runtime_contexts')])
            python('two_row_context', ['--domain', domain])
        elif task == 'runtime-rewrites':
            python('runtime_rewrites', ['--contexts', contexts('runtime_contexts', core=True)])
        elif task == 'single-initializers':
            initializer('rewrite_init_search', edits, True)
        elif task == 'paired-initializers':
            initializer('pair_rewrite_init', edits, False)
    (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
    print('COMPLETE', a.task, flush=True)


if __name__ == '__main__':
    main()
