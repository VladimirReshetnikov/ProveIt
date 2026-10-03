#!/usr/bin/env python3
"""Regenerate mandatory pinned baseline tables without external-release reads."""
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from verify_pins import verify_inputs
ROOT = Path(__file__).resolve().parent
OUTPUTS = ('primitive3.json', 'normalized3.json', 'reversible5.json',
           'reversible2-primitives.json', 'source.json', 'certificates.json',
           'build-stats.json')

def guarded_python(script):
    command = [sys.executable, '-I', '-B']
    if sys.flags.optimize:
        command.append('-O')
    return command + [str(ROOT / 'offline_stage.py'), str(script)]

@contextmanager
def regenerated_baseline():
    verify_inputs()
    expected = json.loads((ROOT / 'baseline/expected-outputs.json').read_text())['files']
    if set(expected) != set(OUTPUTS):
        raise RuntimeError('Incomplete baseline output pin set')
    # The offline stage confines all scratch creation to the replay root.
    scratch = ROOT / '_scratch'
    scratch.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='baseline-', dir=scratch) as directory:
        baseline = Path(directory)
        (baseline / 'dependency').mkdir()
        shutil.copyfile(ROOT / 'dependency/virtual3.json', baseline / 'dependency/virtual3.json')
        shutil.copyfile(ROOT / 'baseline/build_source.py', baseline / 'build_source.py')
        shutil.copyfile(ROOT / 'baseline/loader.py', baseline / 'loader.py')
        process = subprocess.run(guarded_python(baseline / 'build_source.py'),
                                 cwd=ROOT, capture_output=True, text=True)
        if process.returncode:
            raise RuntimeError('Baseline regeneration failed: '+process.stdout+process.stderr)
        for name in OUTPUTS:
            raw = (baseline / name).read_bytes()
            if len(raw) != expected[name]['bytes'] or hashlib.sha256(raw).hexdigest() != expected[name]['sha256']:
                raise RuntimeError('Mandatory frozen baseline hash mismatch: '+name)
        if expected['source.json']['sha256'] != '38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a':
            raise RuntimeError('Wrong predecessor identity')
        yield baseline
    try:
        scratch.rmdir()
    except OSError:
        pass
