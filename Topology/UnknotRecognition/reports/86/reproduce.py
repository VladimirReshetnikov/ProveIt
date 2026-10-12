#!/usr/bin/env python3
"""Run the research package without installing or altering a ProveIt checkout."""
import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
FAST = ROOT / 'repro/Topology/UnknotRecognition/fast'
EDGE = ROOT / 'artifacts/edge_discovery'
INTERFACE = ROOT / 'artifacts/parallelity'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['test', 'replay', 'family', 'enumeration',
                                         'benchmark', 'regina', 'figure', 'pdf'])
    parser.add_argument('--rounds', type=int, default=7)
    args = parser.parse_args()
    env = os.environ.copy()
    extra = env.get('PYTHONPATH')
    env['PYTHONPATH'] = os.pathsep.join(
        [str(FAST), str(EDGE), str(INTERFACE)] + ([extra] if extra else []))
    py = [sys.executable, '-B']
    if args.mode == 'test':
        command = py + ['-m', 'unittest', '-v', 'tests.test_normal_weight_defect',
                        'test_vertex_gate', 'test_parallelity_boundary']
        cwd = FAST
    elif args.mode == 'replay':
        command = py + [str(ROOT / 'verify_artifacts.py')]
        cwd = ROOT
    elif args.mode in ['family', 'enumeration', 'benchmark', 'regina']:
        destination = ROOT / 'reproduced'
        destination.mkdir(exist_ok=True)
        command = py + ['-m', 'normal_orbit_research.weight_defect', args.mode,
                        '--output', str(destination / (args.mode + '.json'))]
        if args.mode == 'benchmark':
            command += ['--rounds', str(args.rounds)]
        cwd = FAST
    elif args.mode == 'figure':
        command = py + [str(ROOT / 'artifacts/plot_benchmarks.py')]
        cwd = ROOT
    else:
        command = ['latexmk', '-pdf', '-interaction=nonstopmode', '-halt-on-error',
                   'unknot_cancellation.tex']
        cwd = ROOT / 'article'
    return subprocess.run(command, cwd=cwd, env=env).returncode


if __name__ == '__main__':
    raise SystemExit(main())
