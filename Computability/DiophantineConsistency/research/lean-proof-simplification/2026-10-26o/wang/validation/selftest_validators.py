#!/usr/bin/env python3
"""Check normal/-O agreement, malformed-input rejection, and read-only defaults."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline', type=Path, default=ROOT.parent / 'baseline')
parser.add_argument('--output', type=Path)
args = parser.parse_args()
REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')

def require(condition, message):
    if not condition:
        raise ValueError(message)

def hashes():
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in ROOT.rglob('*') if p.is_file()}

before = hashes()
results = []
for script, input_name, bad_message in [
    ('measure_boundary_fibers.py', 'WangTiles942Boundary.lean', 'Boundary baseline differs'),
    ('check_boundary_fibers.py', 'WangTiles942Data.lean', 'Data baseline differs')]:
    outputs = []
    for flags in [[], ['-O']]:
        proc = subprocess.run([sys.executable, *flags, str(ROOT/'validation'/script),
                               '--baseline', str(args.baseline)], capture_output=True, text=True)
        require(proc.returncode == 0, script + ' valid input failed: ' + proc.stderr)
        outputs.append(json.loads(proc.stdout))
    require(outputs[0] == outputs[1], script + ' differs under python -O.')
    with tempfile.TemporaryDirectory(prefix='wang-malformed-') as directory:
        fixture = Path(directory)
        (fixture / REL).mkdir(parents=True)
        for name in ['WangTiles942Boundary.lean','WangTiles942Data.lean','WangTiles942Core.lean']:
            shutil.copy2(args.baseline / REL / name, fixture / REL / name)
        damaged = fixture / REL / input_name
        damaged.write_text('MALFORMED_SOURCE\n' + damaged.read_text())
        for flags in [[], ['-O']]:
            proc = subprocess.run([sys.executable, *flags, str(ROOT/'validation'/script),
                                   '--baseline', str(fixture)], capture_output=True, text=True)
            require(proc.returncode != 0 and bad_message in proc.stderr,
                    script + ' failed to reject modified baseline under ' + repr(flags))
    results.append({'script':script, 'normal': 'PASS', 'optimized': 'PASS',
                    'normal_optimized_equal': True, 'malformed_rejected_normal_and_optimized': True})
require(before == hashes(), 'A validator modified its own packaged files despite read-only invocation.')
result = {'status':'PASS', 'checks':results, 'read_only_default_preserved':True,
          'lean_compilation':'NOT RUN'}
rendered = json.dumps(result, indent=2) + '\n'
if args.output is not None:
    args.output.write_text(rendered)
print(rendered, end='')
