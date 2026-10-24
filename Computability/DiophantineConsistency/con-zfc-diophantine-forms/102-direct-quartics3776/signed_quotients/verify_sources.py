#!/usr/bin/env python3
"""Replay the complete frozen natural source, without a network or input ZIP."""
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    src = HERE/'source/upstream'
    pins = json.loads((HERE/'source/SOURCE_PINS.json').read_text())
    verified = {}
    for name, spec in pins['files'].items():
        digest = sha256((src/name).read_bytes()).hexdigest()
        need(digest == spec['candidate_sha256'], 'upstream source mismatch: '+name)
        verified[name] = digest
    python = [sys.executable] + (['-O'] if sys.flags.optimize else [])
    with tempfile.TemporaryDirectory(prefix='conzfc-source-') as temp:
        directory = Path(temp)
        subprocess.run(python+[str(src/'build_equation.py'), '--output', str(directory)],
                       check=True, capture_output=True, text=True)
        parent = (HERE/'source/natural_equation.json').read_bytes()
        need((directory/'equation.json').read_bytes() == parent,
             'complete frozen parent regeneration differs')
        digest = sha256((directory/'expanded_polynomial.json').read_bytes()).hexdigest()
        need(digest == '06912612d90d67209d1554f29f50e45faebead811d2ec9cf7e8f97fa900e0718',
             'complete parent polynomial regeneration differs')
        retained_dir = directory/'retained'
        subprocess.run(python+[str(src/'build_equation.py'), '--keep-linear-wires',
                               '--output', str(retained_dir)],
                       check=True, capture_output=True, text=True)
        need((retained_dir/'equation.json').read_bytes()
             == (HERE/'source/retained/equation.json').read_bytes(),
             'complete retained parent regeneration differs')
        subprocess.run(python+[str(src/'check_equation.py'), '--directory', str(src),
                               '--equation-directory', str(directory),
                               '--output', str(directory/'CHECK.json')],
                       check=True, capture_output=True, text=True)
        subprocess.run(python+[str(src/'audit_power_graph.py'), '--output', str(directory/'POWER.json')],
                       check=True, capture_output=True, text=True)
        calculus = subprocess.run(python+[str(src/'audit_calculus.py')],
                                  check=True, capture_output=True, text=True)
        result = {'status': 'PASS', 'python_optimization': sys.flags.optimize,
                  'verified_source_hashes': verified,
                  'natural_equation_sha256': sha256(parent).hexdigest(),
                  'retained_natural_equation_sha256': sha256((retained_dir/'equation.json').read_bytes()).hexdigest(),
                  'expanded_parent_sha256': digest,
                  'parent_audit': json.loads((directory/'CHECK.json').read_text()),
                  'power_audit': json.loads((directory/'POWER.json').read_text()),
                  'calculus_audit': json.loads(calculus.stdout)}
    target = HERE/'source'/('SOURCE_REPLAY_OPTIMIZED.json' if sys.flags.optimize else 'SOURCE_REPLAY.json')
    target.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print('PASS: seven pinned source files, complete natural polynomial regeneration, '
          'arithmetic audit, 17 power constraints, and 12 literal C222 branches.')


if __name__ == '__main__':
    main()
