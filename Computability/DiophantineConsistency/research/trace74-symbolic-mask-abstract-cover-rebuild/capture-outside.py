#!/usr/bin/env python3
"""Record the direct Mathlib provider; no Lean invocation or transitive claim."""
from pathlib import Path
from hashlib import sha256
import json, os, sys

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
H = Path(__file__).resolve().parent
BASE = Path('/tmp/trace74-conditional-saturation-guard-c4x4yq_y/lib')
PACK = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
CORE = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
stem = 'Mathlib/Data/Nat/Basic'
suffixes = ('.olean', '.olean.private', '.olean.server', '.ilean', '.ir', '.olean.hash', '.olean.private.hash', '.olean.server.hash', '.ilean.hash', '.ir.hash')
sha = lambda p: sha256(Path(p).read_bytes()).hexdigest()
out = H / 'outside-capture.json'
if os.path.lexists(out):
    raise SystemExit('refusing clobber')
selected = None
for root in (BASE, PACK, CORE):
    path = root / (stem + '.olean')
    if os.path.lexists(path):
        if not path.is_file():
            raise SystemExit('invalid shadow: ' + str(path))
        selected = root
        break
if selected != PACK:
    raise SystemExit('unexpected first provider: ' + str(selected))
records = {}
for suffix in suffixes:
    path = PACK / (stem + suffix)
    if os.path.lexists(path):
        if not path.is_file():
            raise SystemExit('invalid companion: ' + str(path))
        records[suffix] = {'path': str(path), 'resolved': str(path.resolve(strict=True)),
                           'sha256': sha(path), 'link': os.readlink(path) if path.is_symlink() else None}
    else:
        records[suffix] = None
if records['.olean']['sha256'] != 'b7313829708c3c06eafa1e8c1d6e8d537c322c675a0c7536c44d31963638c250':
    raise SystemExit('unexpected object hash')
r = {'status': 'PASS', 'module': 'Mathlib.Data.Nat.Basic', 'record': records,
     'capture_sha256': sha(__file__), 'search_order': [str(BASE), str(PACK), str(CORE)],
     'scope': 'one current direct outside bundle; no transitive package ancestry'}
with out.open('x') as f:
    json.dump(r, f, indent=2, sort_keys=True)
    f.write('\n')
print(sha(out))
