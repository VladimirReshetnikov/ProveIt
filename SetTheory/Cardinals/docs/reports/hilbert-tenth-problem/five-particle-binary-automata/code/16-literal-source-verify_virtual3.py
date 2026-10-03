#!/usr/bin/env python3
# Verification conditions are explicit and remain active under python -O.
"""Independent replay of exported literal tables, with symbolic loop-body checks.
The all-input proof is in PROOF.md; affine checks cover every literal instruction.
"""
from pathlib import Path
from collections import Counter
import json, hashlib
R = Path(__file__).resolve().parent / 'dependency'
TM = json.loads((R / 'tm_table.json').read_text())
V = json.loads((R / 'virtual3.json').read_text())
C = json.loads((R / 'macro_certificates.json').read_text())
vr = V['rows']
stats = Counter()
if not set(V['tm_cuts']) == set(TM):
    raise AssertionError('Verification obligation failed')
if not (len(C['tm_macros']) == 29 and {c['state'] for c in C['tm_macros']} == {k for k, v in TM.items() if v is not None}):
    raise AssertionError('Verification obligation failed')
if not (len(C['prime_macros']) == len(vr) and {c['virtual_label'] for c in C['prime_macros']} == set(vr)):
    raise AssertionError('Verification obligation failed')

def aff(c=0, *co):
    return (c,) + tuple(co) + (0,) * (3 - len(co))

def plus(a, c):
    return (a[0] + c,) + a[1:]

def path(rows, start, regs, stops, cover):
    """Exactly execute an affine straight-line body on all x,y,z>=0.
    Each tested register must be identically 0 or have nonnegative coefficients
    and constant >=1. Stops are checked only after at least one instruction.
    """
    label = start
    regs = list(regs)
    n = 0
    while True:
        op, i, *dst = rows[label]
        cover.add(label)
        n += 1
        if op == 'ADD':
            regs[i] = plus(regs[i], 1)
            label = dst[0]
        else:
            a = regs[i]
            if a == (0, 0, 0, 0):
                label = dst[1]
            else:
                if not (a[0] >= 1 and min(a[1:]) >= 0):
                    raise AssertionError((label, a))
                regs[i] = plus(a, -1)
                label = dst[0]
        if label in stops:
            return (label, tuple(regs), n)
        if not n < 100:
            raise AssertionError((start, label))

def assert_path(rows, start, initial, end, final, length, cover):
    actual = path(rows, start, initial, {end}, cover)
    if not actual == (end, tuple(final), length):
        raise AssertionError((start, actual, (end, final, length)))
    stats['symbolic_paths'] += 1
s = (R / 'UniversalTM15x2.tm.txt').read_text().splitlines()[0]
if not hashlib.sha256((R / 'UniversalTM15x2.tm.txt').read_bytes()).hexdigest() == 'ba70ab2c04c68d7ec2d31db4c007d7542c3854d1e02b79a4a5ce07f42fb278ae':
    raise AssertionError('Verification obligation failed')
for i, word in enumerate(s.split('_')):
    for b in (0, 1):
        z = word[b * 3:b * 3 + 3]
        expected = None if z == '---' else [int(z[0]), z[1], z[2]]
        if not TM[chr(65 + i) + str(b)] == expected:
            raise AssertionError('Verification obligation failed')
for rows, n in ((vr, 3),):
    for lab, row in rows.items():
        if not (row[0] in ('ADD', 'SUB') and len(row) == (3 if row[0] == 'ADD' else 4)):
            raise AssertionError('Verification obligation failed')
        if not 0 <= row[1] < n:
            raise AssertionError('Verification obligation failed')
        if not all((d in rows or d == 'HALT' for d in row[2:])):
            raise AssertionError('Verification obligation failed')
    if not 'HALT' not in rows:
        raise AssertionError('Verification obligation failed')
for name, data, regs in [('virtual3', V, ['L', 'R', 'T'])]:
    parsed = {}
    for line in (R / (name + '.txt')).read_text().splitlines():
        if line.startswith('#'):
            continue
        label, body = line.split(': ', 1)
        words = body.split()
        if label == 'HALT':
            if not words == ['HALT']:
                raise AssertionError('Verification obligation failed')
            continue
        if not label not in parsed:
            raise AssertionError('Verification obligation failed')
        parsed[label] = [words[0], regs.index(words[1]), *words[2:]]
    if not parsed == data['rows']:
        raise AssertionError('Verification obligation failed')
vcov = set()
x = aff(0, 1)
y = aff(0, 0, 1)
z = aff(0, 0, 0, 1)
zero = aff()
assert_path(vr, 'init_clear_T', (x, y, plus(z, 1)), 'init_clear_T', (x, y, z), 1, vcov)
assert_path(vr, 'init_clear_T', (x, y, zero), V['tm_cuts']['A0'], (x, y, zero), 1, vcov)
for c in C['tm_macros']:
    a = c['phases_prefix']
    X = c['movement_register']
    Y = c['other_register']
    w = c['write']
    qn = c['next_state']
    if not [w, 'L' if X == 0 else 'R', qn] == TM[c['state']]:
        raise AssertionError('Verification obligation failed')
    if not V['tm_cuts'][c['state']] == a + 'pop0':
        raise AssertionError('Verification obligation failed')

    def vec(xx, yy, tt):
        out = [None, None, tt]
        out[X] = xx
        out[Y] = yy
        return tuple(out)
    assert_path(vr, a + 'pop0', vec(plus(x, 2), y, z), a + 'pop0', vec(x, y, plus(z, 1)), 3, vcov)
    for bit in (0, 1):
        b = a + str(bit) + '_'
        assert_path(vr, a + 'pop0', vec(aff(bit), y, z), b + 'back', vec(zero, y, z), 1 + bit, vcov)
        assert_path(vr, b + 'back', vec(x, y, plus(z, 1)), b + 'back', vec(plus(x, 1), y, z), 2, vcov)
        assert_path(vr, b + 'back', vec(x, y, zero), b + 'push', vec(x, y, zero), 1, vcov)
        assert_path(vr, b + 'push', vec(x, plus(y, 1), z), b + 'push', vec(x, y, plus(z, 2)), 3, vcov)
        assert_path(vr, b + 'push', vec(x, zero, z), b + 'restore', vec(x, zero, z), 1, vcov)
        assert_path(vr, b + 'restore', vec(x, y, plus(z, 1)), b + 'restore', vec(x, plus(y, 1), z), 2, vcov)
        assert_path(vr, b + 'restore', vec(x, y, zero), V['tm_cuts'][qn + str(bit)], vec(x, plus(y, w), zero), 1 + w, vcov)
if not vcov == set(vr):
    raise AssertionError(set(vr) - vcov)
stats['virtual_rows_symbolically_covered'] = len(vcov)
print(json.dumps(dict(status='passed', checks=dict(stats)), indent=2))
