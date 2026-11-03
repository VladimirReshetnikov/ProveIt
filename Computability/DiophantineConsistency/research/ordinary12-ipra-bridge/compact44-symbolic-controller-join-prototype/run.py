#!/usr/bin/env python3
"""Build a proposed same-side join over the symbolic-kernel provider.

This is an exploratory runner, not a frozen transitive-closure or paired audit.
It requires sole use of the Lean slot and inherited prebuilt provider objects.
"""
from hashlib import sha256
from pathlib import Path
from shutil import copyfile
import json
import os
import subprocess
import time

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent
PROJECT = next(p for p in HERE.parents if (p / 'Lean/DiophantineConsistency').is_dir())
PROVIDER = Path('/tmp/compact44-k-radix-cert-01/lib')
PACKAGES = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TEMP = Path('/tmp/ipra-compact44-symbolic-unit-join')
SRC = TEMP / 'src'
LIB = TEMP / 'lib'
OBS = HERE / 'observations'

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

if TEMP.exists() or OBS.exists():
    raise SystemExit('Refusing to overwrite existing build or observations')
(SRC / 'DiophantineConsistency').mkdir(parents=True)
(LIB / 'DiophantineConsistency').mkdir(parents=True)
OBS.mkdir()
source_modules = [
    ('DiophantineConsistency/ArithmeticControllerLift', PROJECT / 'Lean/DiophantineConsistency/ArithmeticControllerLift.lean'),
    ('DiophantineConsistency/ArithmeticControllerDataCompact44', BRIDGE / 'compact44-controller-data-prototype/ArithmeticControllerDataCompact44.lean'),
    ('DiophantineConsistency/ArithmeticConstructionUnitCompact44', BRIDGE / 'compact44-controller-unit-prototype/ArithmeticConstructionUnitCompact44.lean'),
    ('SymbolicKernelResidue', BRIDGE / 'compact44-symbolic-k-residue-prototype/SymbolicKernelResidue.lean'),
    ('CompactSymbolicControllerJoin', HERE / 'CompactSymbolicControllerJoin-DRAFT.lean'),
]
for p in (PROVIDER / 'DiophantineConsistency').iterdir():
    (LIB / 'DiophantineConsistency' / p.name).symlink_to(p)
for module, source in source_modules:
    target = SRC / (module + '.lean')
    copyfile(source, target)
    candidate = LIB / (module + '.olean')
    if candidate.exists() or candidate.is_symlink():
        raise SystemExit(f'Provider shadows intended rebuilt module: {module}')

base_names = ['ArithmeticPow', 'ArithmeticModularCancellation', 'ArithmeticStandardCasts',
              'ArithmeticPackingBlocks', 'CompactSymbolicKernelOpaque']
base = [PROVIDER / 'DiophantineConsistency' / (name + '.olean') for name in base_names]
initial = {str(p): sha(p) for p in [LEAN, *base, *(s for _, s in source_modules)]}
if any(sha(SRC / (module + '.lean')) != initial[str(source)]
       for module, source in source_modules):
    raise SystemExit('A source changed while it was frozen')
env = os.environ.copy()
for key in ('LD_PRELOAD', 'LD_LIBRARY_PATH', 'LD_AUDIT'):
    env.pop(key, None)
env['LEAN_PATH'] = f'{LIB}:{PACKAGES}'
records = []
for module, source in source_modules:
    frozen = SRC / (module + '.lean')
    output = LIB / (module + '.olean')
    safe = module.rsplit('/', 1)[-1]
    deps = subprocess.run([str(LEAN), '--deps', str(frozen)], env=env,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    (OBS / f'{safe}.deps').write_bytes(deps.stdout)
    (OBS / f'{safe}.deps.stderr').write_bytes(deps.stderr)
    if deps.returncode != 0 or deps.stderr:
        raise SystemExit(f'Dependency scan failed: {module}')
    command = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', f'--root={SRC}',
               str(frozen), '-o', str(output)]
    start = time.monotonic()
    try:
        cp = subprocess.run(command, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180, check=False)
        code, content = cp.returncode, cp.stdout
    except subprocess.TimeoutExpired as ex:
        code, content = None, ex.stdout or b''
    log = OBS / f'{safe}.log'
    log.write_bytes(content)
    record = dict(module=module, command=command, exit_code=code,
                  duration_seconds=round(time.monotonic()-start, 3),
                  source_sha256=sha(frozen), log_sha256=sha(log),
                  warning_present=b'warning:' in content,
                  sorry_present=b'sorryAx' in content,
                  object_sha256=sha(output) if code == 0 and output.exists() else None)
    records.append(record)
    (OBS / 'terminal.json').write_text(json.dumps(dict(initial_sha256=initial,
        stages=records, scope='Exploratory same-side rebuild; project/package ancestry inherited.'),
        indent=2, sort_keys=True) + '\n')
    print(json.dumps(record, sort_keys=True), flush=True)
    if code != 0 or b'sorryAx' in content or b'error:' in content or not output.exists():
        raise SystemExit(code if code not in (None, 0) else 1)
if any(sha(p) != initial[str(p)] for p in [LEAN, *base, *(s for _, s in source_modules)]):
    raise SystemExit('An input changed during the build')
