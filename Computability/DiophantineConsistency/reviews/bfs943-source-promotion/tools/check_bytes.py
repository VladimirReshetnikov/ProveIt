#!/usr/bin/env python3
"""BFS row transcription vs the K0 payload, re-pinned to the promoted copy.

Usage: py -I -X utf8 -B check_bytes.py

The same check as `research/direct-bfs-lean-kernel-prototype/check-bytes.py`,
re-pinned to the tree copies `Lean/DiophantineConsistency/BFS943/DirectBFSSymbolicKernel.lean`
(rows) and `Lean/DiophantineConsistency/Compact44/CompactSymbolicKernel.lean`
(slots). It also requires each copy to equal its research source once the
import lines are removed, so the research pin carries over. External finite
transcription comparison, not Lean execution or file binding.
"""
from pathlib import Path
import gzip, hashlib, json, re, sys
if sys.flags.optimize:
    raise SystemExit('optimized Python refused')
D = Path(__file__).resolve().parents[3]
R = D / 'research'
L = D / 'Lean/DiophantineConsistency'
sources = {
    'lean': (L / 'BFS943/DirectBFSSymbolicKernel.lean', '02a242e364fc1653ce05fc07d4fe515cc4e3ce287b76f73ab4ffdf2079f7c800'),
    'lean_research': (R / 'direct-bfs-lean-kernel-prototype/DirectBFSSymbolicKernel.lean',
                      '8a1cd03117bae77e3ed13a853f5bff658ba3acf6ef7dd77bff520cd5cc7f1129'),
    'json': (R / 'indexed-tile-enumeration/TILES.json', 'f06d1b9858281f1adcbc431d3c0df9b07df1a231793629650b2d3c09eac56549'),
    'kernel': (L / 'Compact44/CompactSymbolicKernel.lean', '9b2b73430cbf4578ef4b4c7d4658c9526b7ebdc423263470df907a16b454ba55'),
    'kernel_research': (R / 'ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean',
                        'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae'),
    'payload': (R / 'indexed-tile-enumeration/coefficients/K.bin.gz', '35ad71ca5349bf78c996ac983a7cea6944260ed9f35c61c2b70770f5888d52ce')}


def pin():
    for name, (p, want) in sources.items():
        if hashlib.sha256(p.read_bytes()).hexdigest() != want:
            raise ValueError('hash mismatch ' + name)


def body(p):
    return [l for l in p.read_text(encoding='utf-8').splitlines() if not re.match(r'\s*import\s', l)]


pin()
for a, b in (('lean', 'lean_research'), ('kernel', 'kernel_research')):
    if body(sources[a][0]) != body(sources[b][0]):
        raise ValueError('copy differs from research source beyond imports: ' + a)
text = sources['lean'][0].read_text(encoding='utf-8')
section = text.split('def rows : List (Nat × Nat × Nat × Nat) := [\n', 1)[1].split('  ]\n', 1)[0]
rows = []
for line in section.splitlines():
    m = re.fullmatch(r'  \((\d+), (\d+), (\d+), (\d+)\),', line)
    if m is None:
        raise ValueError('row syntax')
    rows.append(list(map(int, m.group(1, 2, 3, 4))))
if len(rows) != 943 or rows != json.loads(sources['json'][0].read_text(encoding='utf-8')):
    raise ValueError('row transcription')
src = sources['kernel'][0].read_text(encoding='utf-8')
m = re.search(r'^def slots : List ℕ := \[([0-9,]+)\]$', src, re.M)
if m is None:
    raise ValueError('slots syntax')
slots = list(map(int, m.group(1).split(',')))
if len(slots) != 41 or len(set(slots)) != 41:
    raise ValueError('slots')
P = lambda n: 1 << (67 * n)


def coeff(row):
    w, n, e, s = row
    if not (0 <= w < 256 and 0 <= n < 512 and 0 <= e < 256 and 0 <= s < 512):
        raise ValueError('width')
    val = w + (1 << 8) * n + (1 << 17) * e + (1 << 25) * s + 127 * (1 << 34)
    return 1 + (1 << 10) * ((1 << 41) - val)


def reflected(e, c):
    return c * (P(4393 - e) + P(5495 - e))


k = (sum(P(e) for e in (30, 62, 1100, 2201)) + sum(reflected(i, coeff(row)) for i, row in enumerate(rows))
     + sum(reflected(e, 1 << (10 + j)) for j, e in enumerate(slots)) + P(8807) * P(42))
raw = k.to_bytes((k.bit_length() + 7) // 8, 'little')
target = gzip.decompress(sources['payload'][0].read_bytes())
sha = hashlib.sha256(raw).hexdigest()
if raw != target or sha != '0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f':
    raise ValueError('bytes mismatch')
pin()
print(json.dumps({'status': 'PASS_EXTERNAL_RECIPE_BYTES', 'rows': len(rows), 'slots': len(slots), 'raw_sha256': sha,
                  'raw_bytes': len(raw), 'bits': k.bit_length(),
                  'scope': 'Python transcription of the promoted copies; neither Lean evaluation nor formal file binding'},
                 sort_keys=True))
