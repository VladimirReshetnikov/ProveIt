#!/usr/bin/env python3
"""Run pinned arithmetic checks in isolated fresh copies and preserve the payload."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, stat, subprocess, sys, tempfile

ROOT = Path(__file__).resolve().parent

def fail(message):
    raise RuntimeError(message)

def snapshot():
    result = {}
    for p in sorted(ROOT.rglob('*')):
        if p.is_symlink():
            fail('Symlink in release')
        if p.is_file():
            s = p.stat()
            result[p.relative_to(ROOT).as_posix()] = (hashlib.sha256(p.read_bytes()).hexdigest(), stat.S_IMODE(s.st_mode), s.st_mtime_ns)
    return result

def typed_equal(actual, expected, label='receipt'):
    if type(actual) is not type(expected):
        fail(label + ': type mismatch')
    if isinstance(expected, dict):
        if set(actual) != set(expected):
            fail(label + ': key mismatch')
        for key in expected:
            typed_equal(actual[key], expected[key], label + '.' + key)
    elif isinstance(expected, list):
        if len(actual) != len(expected):
            fail(label + ': length mismatch')
        for i, (a, b) in enumerate(zip(actual, expected)):
            typed_equal(a, b, label + '[' + str(i) + ']')
    elif actual != expected:
        fail(label + ': value mismatch')

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir', type=Path, required=True)
args = parser.parse_args()
out = args.output_dir.resolve()
if out == ROOT or ROOT in out.parents:
    fail('Outputs must be outside the release')
if out.exists() and any(out.iterdir()):
    fail('Output directory must be absent or empty')
out.mkdir(parents=True, exist_ok=True)
before = snapshot()
expected_original = json.loads((ROOT/'verification/expected-arithmetic.json').read_text())
expected_independent = json.loads((ROOT/'verification/expected-independent.json').read_text())
expected_timed = json.loads((ROOT/'verification/expected-timed.json').read_text())
# Verify the expected schemas rather than relying only on ordinary JSON equality.
if type(expected_original.get('seed')) is not int or expected_original['seed'] != 20261003:
    fail('Invalid fixed-seed receipt schema')
for r, key in ((expected_original, 'checks'), (expected_independent, 'counts'), (expected_timed, 'counts')):
    if type(r.get(key)) is not dict or not all(type(v) is int for v in r[key].values()):
        fail('Invalid integer-count receipt schema')
records = {}
for mode, flags in (('normal', []), ('optimized', ['-O'])):
    with tempfile.TemporaryDirectory(prefix='report29-' + mode + '-') as tmp:
        work = Path(tmp)
        for name in ('audit_arithmetic.py', 'check_independent_arithmetic.py', 'PROOF.md'):
            shutil.copy2(ROOT/'scientific'/name, work/name)
        shutil.copy2(ROOT/'scientific/timed/check_corollary.py', work/'check_corollary.py')
        commands = [('original', [str(work/'audit_arithmetic.py')], expected_original),
                    ('independent', [str(work/'check_independent_arithmetic.py'), '--proof', str(work/'PROOF.md')], expected_independent),
                    ('timed', [str(work/'check_corollary.py')], expected_timed)]
        records[mode] = {}
        for label, tail, expected in commands:
            completed = subprocess.run([sys.executable, '-I', '-B', *flags, *tail], cwd=work, text=True, capture_output=True, check=False)
            if completed.returncode:
                fail(label + ' ' + mode + ' exited ' + str(completed.returncode) + ': ' + completed.stderr)
            got = json.loads(completed.stdout)
            typed_equal(got, expected, label + ' ' + mode)
            if label == 'original':
                typed_equal(json.loads((work/'arithmetic-results.json').read_text()), expected, label + ' written receipt')
            if label == 'timed':
                typed_equal(json.loads((work/'check-results.json').read_text()), expected, label + ' written receipt')
            records[mode][label] = got
            (out/(label + '-' + mode + '.json')).write_text(json.dumps(got, indent=2, sort_keys=True) + '\n')
            (out/(label + '-' + mode + '.log')).write_text(completed.stdout + completed.stderr)
typed_equal(records['normal'], records['optimized'], 'normal versus optimized')
# Explicitly exercise a type-only mismatch that ordinary Python equality accepts.
probe = json.loads(json.dumps(expected_original))
probe['checks']['hull_hole_regression'] = True
try:
    typed_equal(probe, expected_original, 'boolean regression')
except RuntimeError:
    type_regression = 'PASS'
else:
    fail('Boolean masquerading as integer was not rejected')
after = snapshot()
if before != after:
    fail('Release bytes, modes or modification times changed')
summary = {'status': 'PASS', 'normal_optimized_exact_typed_equality': True, 'payload_bytes_modes_mtimes_preserved': True,
           'boolean_integer_type_regression': type_regression,
           'scope': 'Finite arithmetic checks only; no general CA compiler or formal proof'}
(out/'replay-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
