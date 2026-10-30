#!/usr/bin/env python3
"""Overlay the independently accepted fstIdx and fold providers for replay.

The called replay authenticates every local source and every resolved parent
object in its 81-module graph, including both explicitly overlaid modules.
Foundation and Mathlib remain inherited.
"""
from pathlib import Path
import argparse, subprocess, tempfile
p = argparse.ArgumentParser()
p.add_argument('--local', type=Path, required=True)
p.add_argument('--fold', type=Path, required=True)
a = p.parse_args()
local = a.local.resolve()
fold = a.fold.resolve()
parent = Path(tempfile.mkdtemp(prefix='pra-fstidx-family-overlay-')) / 'lib'
dst = parent / 'DiophantineConsistency'
dst.mkdir(parents=True)
for f in (local / 'DiophantineConsistency').glob('*.olean'):
    (dst / f.name).symlink_to(f.resolve())
for name in ('PRAWitnessFold', 'PRAWitnessFoldChecks'):
    obj = fold / 'DiophantineConsistency' / (name + '.olean')
    if not obj.is_file():
        raise RuntimeError(f'missing fold object: {obj}')
    target = dst / obj.name
    if target.exists() or target.is_symlink():
        target.unlink()
    target.symlink_to(obj.resolve())
foundation = local / 'Foundation'
if not foundation.is_dir():
    raise RuntimeError(f'missing Foundation provider: {foundation}')
(parent / 'Foundation').symlink_to(foundation.resolve(), target_is_directory=True)
print('OVERLAY', parent, flush=True)
script = Path(__file__).resolve().parent / 'replay.py'
raise SystemExit(subprocess.call(['python3', str(script), '--parent', str(parent)]))
