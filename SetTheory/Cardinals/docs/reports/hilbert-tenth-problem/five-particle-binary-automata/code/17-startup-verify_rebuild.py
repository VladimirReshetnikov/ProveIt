#!/usr/bin/env python3
"""Fresh exact new/baseline rebuilds with mandatory pins; no sibling reads."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
from baseline_support import regenerated_baseline, guarded_python, OUTPUTS
from verify_pins import verify_inputs
ROOT = Path(__file__).resolve().parent
verify_inputs()
def record(path):
    raw = path.read_bytes()
    return dict(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest())
def save(name, value):
    (ROOT / name).write_text(json.dumps(value, indent=2)+'\n')
scratch = ROOT / '_scratch'
scratch.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='new-rebuild-', dir=scratch) as directory:
    rebuilt = Path(directory)
    (rebuilt / 'dependency').mkdir()
    shutil.copyfile(ROOT / 'build_source.py', rebuilt / 'build_source.py')
    shutil.copyfile(ROOT / 'dependency/virtual3.json', rebuilt / 'dependency/virtual3.json')
    result = subprocess.run(guarded_python(rebuilt / 'build_source.py'), cwd=ROOT,
                            text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError('New rebuild failed: '+result.stdout+result.stderr)
    records = {}
    for name in OUTPUTS:
        if (rebuilt / name).read_bytes() != (ROOT / name).read_bytes():
            raise RuntimeError('Byte-exact rebuild mismatch: '+name)
        records[name] = record(ROOT / name)
    save('byte-exact-rebuild-receipt.json', dict(status='PASS', scope='Fresh isolated new-generator rebuild; seven outputs byte-for-byte identical to mandatory pinned supplied artifacts', files=records))
with regenerated_baseline() as baseline:
    for name in ('primitive3.json', 'normalized3.json', 'build-stats.json', 'dependency/virtual3.json'):
        if (baseline / name).read_bytes() != (ROOT / name).read_bytes():
            raise RuntimeError('Unchanged data/count layer mismatch: '+name)
    save('baseline-rebuild-receipt.json', dict(status='PASS', scope='Fresh regeneration of all seven historical baseline outputs from bundled pinned original generator; mandatory original SHA-256 values verified. This is not a recheck of the entire external predecessor release.', baseline_files={name:record(baseline / name) for name in OUTPUTS}, unchanged_layers=['primitive3.json', 'normalized3.json', 'build-stats.json', 'dependency/virtual3.json']))
try:
    scratch.rmdir()
except OSError:
    pass
verify_inputs()
print('PASS: seven new outputs byte-exact; seven baseline outputs match mandatory historical pins')
