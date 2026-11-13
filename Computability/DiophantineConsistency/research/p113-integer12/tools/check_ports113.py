#!/usr/bin/env python3
"""Check that package 113's six coefficients are package 138's, hence `P138Ports.ports6`.

Usage: py -I -X utf8 -B check_ports113.py

`integer12_saturated/rational.json` (the 1084/123 equation of `P113Syntax`) does not contain the
numeric values of its six fixed integers. Its nodes 12..17 are symbolic leaves
`["coefficient", name]` for `beta K0 MC MF cone_A cone_B`, and its field `coefficient_binding`
names `coefficients/BINDING.json`. The package's `INHERITED_SOURCE_PINS.json` (`retained_files`)
pins that file and the six payloads `coefficients/*.bin.gz` by SHA-256.

The check, link by link:

1. the JSON's SHA-256 (the pin of `gen_literal113.py`), its coefficient leaves (names, order,
   node numbers) and `coefficient_binding`;
2. the seven pins of `INHERITED_SOURCE_PINS.json` (`BINDING.json` and the six payloads) are
   equal to the pins of package 138's `integer11/RESTORED_DEPENDENCIES.json` for the same
   relative paths, and the repository copies named there exist and have those SHA-256 values.

`research/p138-integer11/tools/check_ports138.py` checks that those payloads are, as integers,
`P138Ports.ports6 0..5`. Together the two checks bind package 113's equation to the Lean ports
used by `IPRAInteger113.expression`. This is finite external evidence, not a Lean theorem.
"""
from pathlib import Path
import hashlib, json, sys

HERE = Path(__file__).resolve()
DC = HERE.parents[3]
REPO = HERE.parents[5]
PKG = DC / 'con-zfc-diophantine-forms/113-saturated-pell/integer12_saturated'
JSON = PKG / 'rational.json'
PIN = '4afd94ea0580a4527b5b9320528e3c198539ad2698f7d3e453e76e8e2667ba50'
PINS = PKG / 'INHERITED_SOURCE_PINS.json'
REST138 = DC / 'con-zfc-diophantine-forms/138-semantic-signs/integer11/RESTORED_DEPENDENCIES.json'
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
PATHS = ['coefficients/BINDING.json'] + [f'coefficients/{n}.bin.gz' for n in PORTS]

FAIL = []


def need(ok, msg):
    print(('  ok   ' if ok else '  FAIL ') + msg)
    if not ok:
        FAIL.append(msg)
    return ok


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


print('1. the equation')
raw = JSON.read_bytes()
need(hashlib.sha256(raw).hexdigest() == PIN, f'{JSON.name} SHA-256 {PIN[:16]}...')
d = json.loads(raw)
leaves = [(i, n[1]) for i, n in enumerate(d['nodes'])
          if isinstance(n, list) and n and n[0] == 'coefficient']
need(leaves == [(12 + k, n) for k, n in enumerate(PORTS)],
     'coefficient leaves are nodes 12..17 = beta K0 MC MF cone_A cone_B')
need(d.get('coefficient_binding') == 'coefficients/BINDING.json',
     'coefficient_binding = coefficients/BINDING.json')
need(d.get('variables') == ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 't', 's'],
     'twelve variables j C z h r v w T c n t s')

print('2. the pins agree with package 138 and the repository copies')
pins113 = json.loads(PINS.read_text(encoding='utf-8'))['retained_files']
rest138 = json.loads(REST138.read_text(encoding='utf-8'))
for rel in PATHS:
    a = pins113.get(rel)
    b = rest138.get(rel, {}).get('sha256')
    need(a is not None and a == b, f'{rel}: 113 pin = 138 pin ({(a or "missing")[:16]}...)')
    copy = rest138.get(rel, {}).get('repository_path')
    if need(copy is not None and (REPO / copy).is_file(), f'{rel}: repository copy {copy}'):
        need(sha(REPO / copy) == a, f'{rel}: repository copy has the pinned SHA-256')

print('PASS' if not FAIL else f'FAIL ({len(FAIL)})')
sys.exit(1 if FAIL else 0)
