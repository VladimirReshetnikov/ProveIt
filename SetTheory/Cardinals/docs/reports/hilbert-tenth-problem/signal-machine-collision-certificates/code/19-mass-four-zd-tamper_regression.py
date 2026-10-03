#!/usr/bin/env python3
"""Exercise the release preflight in temporary copies; never run altered science."""
from pathlib import Path
import hashlib, json, shutil, subprocess, tempfile
ROOT = Path(__file__).resolve().parent

def reseal(root):
    lines = []
    for p in sorted(root.rglob('*')):
        if p.is_file() and not p.is_symlink() and p.name != 'SHA256SUMS':
            lines.append(hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(root).as_posix())
    (root/'SHA256SUMS').write_text('\n'.join(lines)+'\n')

def run(root):
    return subprocess.run(['sh', str(root/'reproduce.sh'), '--verify-only'], cwd=root.parent, text=True, capture_output=True)

cases = ['changed_science', 'resealed_changed_science', 'missing_required_script', 'resealed_missing_required_script', 'extra_payload', 'symlink_payload']
results = {}
with tempfile.TemporaryDirectory(prefix='report29-tamper-') as temp:
    for name in cases:
        target = Path(temp)/name
        shutil.copytree(ROOT, target, copy_function=shutil.copy2)
        p = target/'scientific/audit_arithmetic.py'
        if name in ('changed_science','resealed_changed_science'):
            p.write_text(p.read_text() + '\nraise RuntimeError("tampered source executed")\n')
        elif name in ('missing_required_script','resealed_missing_required_script'):
            p.unlink()
        elif name == 'extra_payload':
            (target/'unexpected.txt').write_text('extra payload\n')
        else:
            p.unlink(); p.symlink_to(ROOT/'scientific/audit_arithmetic.py')
        if name.startswith('resealed_'):
            reseal(target)
        result = run(target)
        if result.returncode == 0:
            raise RuntimeError('Tamper unexpectedly accepted: ' + name)
        if 'tampered source executed' in result.stderr:
            raise RuntimeError('Altered scientific code ran')
        results[name] = 'REJECTED_BEFORE_HELPER_EXECUTION'
clean = run(ROOT)
if clean.returncode:
    raise RuntimeError('Clean inventory failed: ' + clean.stderr)
print(json.dumps({'status':'PASS','cases':results,'clean_inventory':'PASS'},indent=2,sort_keys=True))
