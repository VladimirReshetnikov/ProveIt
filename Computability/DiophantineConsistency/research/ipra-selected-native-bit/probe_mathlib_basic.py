#!/usr/bin/env python3
"""Isolated reproducibility probe; never installs or trusts a rebuilt provider."""
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

checkout = Path('/home/codex/src/Proofs/.lake/packages/mathlib')
revision = '81a5d257c8e410db227a6665ed08f64fea08e997'
source_rel = 'Mathlib/Computability/Primrec/Basic.lean'
source_sha = '244592f117afc0cd69eee5ba274ffb62acc87a5faa177e38085cbdb1ea2e76c6'
original_sha = '33e972e2176e5ad98403651c38725d34843e5ed67a60e41e9986dd12a8d9eb6a'
lean = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
package = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
out = Path('/tmp/ipra-mathlib-primrec-basic-probe-01')
if out.exists() or out.is_symlink():
    raise ValueError('probe output already exists')
if shutil.disk_usage('/tmp').free < 4 * 1024**3:
    raise ValueError('disk reserve too low')
h = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
head = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=checkout, check=True,
                      capture_output=True, text=True).stdout.strip()
assert head == revision
data = subprocess.run(['git', 'show', revision + ':' + source_rel], cwd=checkout,
                      capture_output=True, check=True).stdout
assert hashlib.sha256(data).hexdigest() == source_sha == h(checkout / source_rel)
original = package / 'Mathlib/Computability/Primrec/Basic.olean'
assert original.is_file() and h(original) == original_sha
source = out / 'src' / source_rel
target = out / 'lib/Mathlib/Computability/Primrec/Basic.olean'
source.parent.mkdir(parents=True)
target.parent.mkdir(parents=True)
source.write_bytes(data)
env = dict(os.environ, LEAN_PATH=str(package), LEAN_NUM_THREADS='1')
for key in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
    env.pop(key, None)
deps = subprocess.run([str(lean), '-R', str(out / 'src'), '--deps', str(source)],
                      cwd=out / 'src', env=env, capture_output=True, text=True)
if deps.returncode != 0 or deps.stderr:
    raise RuntimeError(('dependency query failed', deps.returncode, deps.stderr))
paths = [Path(line) for line in deps.stdout.splitlines()]
assert paths and all(x.is_absolute() and x.is_file() for x in paths)
before = {str(x): {'realpath': str(x.resolve(strict=True)), 'sha256': h(x)} for x in paths}
cmd = ['ionice', '-c', '3', 'nice', '-n', '19', str(lean), '-R', str(out / 'src'),
       '-M8000', '-j1', '-Dpp.unicode.fun=true', '-DautoImplicit=false',
       '-DmaxSynthPendingDepth=3', '-o', str(target), str(source)]
proc = subprocess.run(cmd, cwd=out / 'src', env=env, capture_output=True, text=True)
(out / 'process.log').write_text(proc.stdout + proc.stderr)
after = {str(x): {'realpath': str(x.resolve(strict=True)), 'sha256': h(x)} for x in paths}
assert before == after and h(original) == original_sha and h(source) == source_sha
rebuilt = h(target) if target.is_file() else None
result = {'checkout_revision': revision, 'source_sha256': source_sha,
          'original_olean_sha256': original_sha, 'rebuilt_olean_sha256': rebuilt,
          'byte_identical': rebuilt == original_sha, 'command': cmd,
          'observed_lean_exit_code': proc.returncode, 'dependencies_before_after': before,
          'process_log_sha256': h(out / 'process.log'),
          'scope': 'Isolated point-in-time reproduction using inherited package imports; no provider mutation, transitive provenance proof or permission to mix artifacts.'}
(out / 'observation.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print('MATHLIB_BASIC_PROBE', proc.returncode, result['byte_identical'], rebuilt)
if proc.returncode:
    raise SystemExit(proc.returncode)
