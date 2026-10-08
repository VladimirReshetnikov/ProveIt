#!/usr/bin/env python3
"""Compare frozen and corrected pipe transport on the recorded large payload.

The old outcome depends on the Python runtime. Only the corrected outcome is
required to complete. This is a local protocol check, not a knot benchmark.
"""
import importlib.util
import json
from pathlib import Path
import sys
from time import monotonic

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'fast'))
from fastunknot import normal_surface as corrected

spec = importlib.util.spec_from_file_location(
    'frozen_normal_surface', HERE / 'normal_surface_before_pipe_thread.py')
frozen = importlib.util.module_from_spec(spec)
spec.loader.exec_module(frozen)

command = [sys.executable, '-B', '-c',
           'import sys,time;time.sleep(.12);data=sys.stdin.read();'
           'sys.stdout.write(data);sys.stderr.write("note")']
payload = 'x' * 500000
rows = []
for name, module in [('frozen', frozen), ('corrected', corrected)]:
    start = monotonic()
    try:
        code, output, errors = module._invoke(command, payload, start + 3, lambda: None)
        assert (code, output, errors) == (0, payload, 'note')
        row = dict(implementation=name, status='COMPLETE', seconds=monotonic()-start)
    except module.NormalTimeout:
        row = dict(implementation=name, status='TIMEOUT', seconds=monotonic()-start)
        if name == 'corrected':
            raise
    rows.append(row)
print(json.dumps(dict(python=sys.version, payload_bytes=len(payload), results=rows), indent=2))
