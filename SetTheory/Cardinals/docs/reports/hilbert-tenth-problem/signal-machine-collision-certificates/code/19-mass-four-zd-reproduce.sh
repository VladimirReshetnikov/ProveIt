#!/bin/sh
# Trusted bootstrap: verify exact required inventory and pins before any helper.
set -eu
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 -I -B - "$ROOT" "$@" <<'PREFLIGHT'
from pathlib import Path, PurePosixPath
import hashlib, json, os, re, subprocess, sys
root = Path(sys.argv[1]).resolve()
args = sys.argv[2:]
REQUIRED = ('README.md', 'build.sh', 'replay.py', 'report29.pdf', 'report29.tex', 'reproduce.sh', 'scientific/PROOF.md', 'scientific/audit.md', 'scientific/audit_arithmetic.py', 'scientific/check_independent_arithmetic.py', 'scientific/independent-review.md', 'scientific/literature.md', 'scientific/timed/PROOF.md', 'scientific/timed/REVIEW.md', 'scientific/timed/check_corollary.py', 'tamper_regression.py', 'verification/expected-arithmetic.json', 'verification/expected-independent.json', 'verification/expected-timed.json', 'verification/source-lineage.json')
PINNED = {'replay.py': '1f53c0c812e2510beea2f2956f800bd8c16e6aa91c3f3c43f23bc5e634a3684d', 'scientific/PROOF.md': 'a2cc2bda22d1f3a68435f0f3f7b1c694278e6941f46cdd2ad3de69e512124511', 'scientific/audit.md': '95f3e078434c80fb2b7c09ccb12817c006a9958e9c49dd917dd0f92f555e20d3', 'scientific/audit_arithmetic.py': 'af7dc6b0916b5fe3ff3cf46f7138d81485012c42d1b586641b9fe5fe63068828', 'scientific/check_independent_arithmetic.py': 'dbff822823d532bc7c453d29f9af3ee4fe4debb0ef7120c1121b5807bcc3672c', 'scientific/independent-review.md': 'bb5f4b9964437baf9c1b4b3544c73182f0db7d95915a4f22a2c710081d868511', 'scientific/literature.md': 'b082a5f89db30fc3c75dba517ba3f5c0ad2d164d3e931bcb1fa6429f059c3930', 'scientific/timed/PROOF.md': '103fe38f7c6d941995e579d7d73dd42ab3836a012666ba16858b158ff698d4c5', 'scientific/timed/REVIEW.md': 'a1412fb003fc1d43a32aa4c0461babdc3e07b02ce067f9fd9ea87d04e1a3a0b8', 'scientific/timed/check_corollary.py': 'a41f0e559525fc94790bbe61498fcbb2cc68d3650633ca6e7fe191773849f144', 'tamper_regression.py': 'af34ce31814fcf6ea7d76b8e978a66314e38ec41bba833a7d51264e2a6dc6356', 'verification/expected-arithmetic.json': 'dbd798c15c05610d1f748b618edac19b62df139f10f6a01b1e459334b71b393c', 'verification/expected-independent.json': '09e2d258d76316f26e6d53723396cc6498c732ec66bd5ddf7470974741e17d0d', 'verification/expected-timed.json': '02c7efe9d4ed95d1fa271985f4e85a15b6be81060c86bff7b4e4845c3ada7e86', 'verification/source-lineage.json': '143dc15af6bbc1a291add327c3a473bff076754d7fd3cc7aa3e3b30c59892144'}
def reject(message):
    raise SystemExit('Preflight rejected: ' + message)
if not ((len(args) == 1 and args[0] == '--verify-only') or (len(args) == 2 and args[0] == '--output-dir')):
    reject('Use --verify-only or --output-dir EXTERNAL_DIRECTORY')
actual = set()
for p in root.rglob('*'):
    if p.is_symlink():
        reject('symlink payload')
    if p.is_file():
        actual.add(p.relative_to(root).as_posix())
if actual != set(REQUIRED) | {'SHA256SUMS'}:
    reject('required inventory mismatch: ' + str(sorted(actual ^ (set(REQUIRED)|{'SHA256SUMS'}))))
expected = {}
for line in (root/'SHA256SUMS').read_text(encoding='ascii').splitlines():
    try:
        digest, name = line.split('  ', 1)
    except ValueError:
        reject('invalid manifest syntax')
    path = PurePosixPath(name)
    if not re.fullmatch('[0-9a-f]{64}', digest) or path.is_absolute() or '..' in path.parts or str(path) != name or name in expected:
        reject('invalid manifest entry')
    expected[name] = digest
if set(expected) != set(REQUIRED):
    reject('manifest inventory differs from independently required payloads')
for name in REQUIRED:
    digest = hashlib.sha256((root/name).read_bytes()).hexdigest()
    if digest != expected[name]:
        reject('manifest digest mismatch: ' + name)
    if name in PINNED and digest != PINNED[name]:
        reject('independent pin mismatch: ' + name)
print('Preflight PASS: exact inventory, manifest, independent science and helper pins', flush=True)
if args == ['--verify-only']:
    raise SystemExit(0)
out = Path(args[1]).resolve()
if out == root or root in out.parents:
    reject('output directory must be external')
subprocess.run([sys.executable, '-I', '-B', str(root/'replay.py'), *args], check=True)
completed = subprocess.run([sys.executable, '-I', '-B', str(root/'tamper_regression.py')], text=True, capture_output=True, check=True)
result = json.loads(completed.stdout)
if type(result) is not dict or result.get('status') != 'PASS':
    reject('tamper regression failed')
(out/'tamper-regression.json').write_text(completed.stdout)
print(completed.stdout, end='')
print('Replay PASS: all science ran in isolated normal and optimized copies')
PREFLIGHT
