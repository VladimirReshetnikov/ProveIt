#!/usr/bin/env python3
"""External direct-sum review of the Horner residue; no Lean execution."""
from hashlib import sha256
from pathlib import Path
import json
import re
import sys

if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is rejected')

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'research/ordinary12-ipra-bridge'
REVIEWED = {
    'compact44-symbolic-k-residue-prototype/SymbolicKernelResidue.lean':
        '7d0d922b649f3690110ef5cfc61e3ed00136fbb4f0e1513d48cc4e7a577adb67',
    'compact44-symbolic-k-residue-prototype/observations/attempt02.lean':
        '7d0d922b649f3690110ef5cfc61e3ed00136fbb4f0e1513d48cc4e7a577adb67',
    'compact44-symbolic-k-residue-prototype/observations/attempt02.log':
        'cf8df1da457ca66ff25c1ace58272d609336508f9a67ef06d4c4a4ac452e40bb',
    'compact44-symbolic-k-residue-prototype/observations/attempt02.json':
        'ee9c8dec6f1b7e051263be04902e67f6d257c25762254972b5a50b876b08229e',
    'compact44-symbolic-kernel-param-prototype/CompactSymbolicKernelOpaque.lean':
        'fbef8642de957bb39493607cb67edda418f53332af5a92ee594a2a437241e0b8',
    'compact44-943-table-prototype/Compact943Data.lean':
        '10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8',
    'compact44-coefficient-mass-prototype/CompactCoefficientMass.lean':
        'ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e',
    'compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean':
        'f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae',
    'compact44-controller-unit-prototype/ArithmeticConstructionUnitCompact44.lean':
        '3f72112b29fe4d70b7896f541efbe9503b89a364de93137fcda4168288f970e9',
    'compact44-controller-data-prototype/ArithmeticControllerDataCompact44.lean':
        '8f28cce9e32b29bd3fd70ef193c46730aee3b2664e92037ce594ce0638c2f02c',
}

def require(condition, reason):
    if not condition:
        raise ValueError(reason)

def check_hashes():
    for relative, expected in REVIEWED.items():
        require(sha256((SRC / relative).read_bytes()).hexdigest() == expected,
                'changed reviewed source or log: ' + relative)

check_hashes()
table = (SRC / 'compact44-943-table-prototype/Compact943Data.lean').read_text()
begin, end = '-- BEGIN PINNED ORDERED ROWS\n', '\n-- END PINNED ORDERED ROWS'
require(table.count(begin) == 1 and table.count(end) == 1, 'row markers')
lines = table.split(begin)[1].split(end)[0].splitlines()
rows = []
for i, line in enumerate(lines):
    m = re.fullmatch(r'  \((\d+), (\d+), (\d+), (\d+)\)(,?)', line)
    require(m is not None and m.group(5) == (',' if i < 942 else ''), 'row syntax')
    rows.append(tuple(map(int, m.group(1, 2, 3, 4))))
source = (SRC / 'compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean').read_text()
match = re.search(r'^def slots : List ℕ := \[([\d,]+)\]$', source, re.M)
require(match is not None, 'slot syntax')
slots = list(map(int, match.group(1).split(',')))
require(len(rows) == 943 and len(slots) == 41 and all(e < 4393 for e in slots),
        'table count or slot bounds')

modulus = 342946332593
radix = pow(2, 67, modulus)
def payload(t):
    w, n, e, s = t
    return w + 2**8*n + 2**17*e + 2**25*s + 127*2**34
values = list(map(payload, rows))
require(all(v <= 2**41 for v in values), 'natural subtraction needs truncation')
selectors = sum((1 + 2**10 * (2**41 - values[i])) *
                (pow(radix, 4393-i, modulus) + pow(radix, 5495-i, modulus))
                for i in range(943)) % modulus
copies = sum(pow(2, 10+i, modulus) *
             (pow(radix, 4393-e, modulus) + pow(radix, 5495-e, modulus))
             for i, e in enumerate(slots)) % modulus
bare = sum(pow(radix, e, modulus) for e in (30, 62, 1100, 2201, 8849)) % modulus
actual = (radix, selectors, copies, bare, (selectors + copies + bare) % modulus)
expected = (139640128744, 33533167632, 299839741459, 294472239397, 284898815895)
require(actual == expected, 'direct-sum residues')
receipt = json.loads((SRC / 'compact44-symbolic-k-residue-prototype/observations/attempt02.json').read_text())
require(receipt['exit_code'] == 0 and receipt['object_sha256'] ==
        'e3d3a2d356e45a9b742ccaf609792b2a7bcfdedf475ed4de0b31ee4e22e67302',
        'author observation differs')
check_hashes()
print(json.dumps({'status': 'PASS_DIRECT_SUM_SOURCE_REVIEW', 'rows': len(rows),
                  'slots': len(slots), 'radix_selectors_copies_bare_total': actual,
                  'scope': 'external direct-sum calculation and source inspection; no Lean replay'},
                 sort_keys=True))
