#!/usr/bin/env python3
"""External check of the proposed Horner decomposition, not a Lean proof."""
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
table = (ROOT / 'compact44-943-table-prototype/Compact943Data.lean').read_text()
table = table.split('-- BEGIN PINNED ORDERED ROWS', 1)[1].split('-- END PINNED ORDERED ROWS', 1)[0]
rows = [tuple(map(int, t)) for t in re.findall(r'\((\d+), (\d+), (\d+), (\d+)\)', table)]
slots_file = (ROOT / 'compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean').read_text()
slots_match = re.search(r'def slots : List ℕ := \[([^\]]+)\]', slots_file)
if slots_match is None:
    raise ValueError('Cannot find slot list')
slots = list(map(int, re.findall(r'\d+', slots_match.group(1))))
if len(rows) != 943 or len(slots) != 41:
    raise ValueError('Unexpected table or slot count')
mod = 342946332593
radix = pow(2, 67, mod)
value = lambda a, b, c, d: a + 2**8*b + 2**17*c + 2**25*d + 127*2**34
z = 0
for row in rows:
    v = value(*row)
    if not 0 < v < 2**41:
        raise ValueError('Unexpected tile value')
    z = (z*radix + 1 + 2**10*(2**41-v)) % mod
copies = sum(pow(2, 10+i, mod) * (pow(radix, 4393-e, mod) +
                                      pow(radix, 5495-e, mod))
             for i, e in enumerate(slots)) % mod
bare = sum(pow(radix, e, mod) for e in (30, 62, 1100, 2201, 8849)) % mod
selectors = z*(pow(radix, 3451, mod) + pow(radix, 4553, mod)) % mod
actual = (radix, z, selectors, copies, bare, (selectors+copies+bare) % mod)
expected = (139640128744, 294576924025, 33533167632,
            299839741459, 294472239397, 284898815895)
if actual != expected:
    raise ValueError(f'Unexpected modular values: {actual!r}')
print('PASS radix, Horner selector, selector bands, copy bands, bare+DR, kernel:', *actual)
print('Scope: external manually transcribed arithmetic; no Lean theorem established')
