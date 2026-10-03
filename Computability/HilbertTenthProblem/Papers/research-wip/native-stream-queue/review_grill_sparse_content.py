#!/usr/bin/env python3
"""Independent complete-source audit of the sparse Grill content row."""
if not __debug__:
    raise RuntimeError('Run without -O')
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
import types

SOURCE_PIN = '3c2d0cf875f82e45062334dc8b42cb033d909afed5204bb9abd9547cff0e16f7'
HELPER_PIN = '5d552d1583400c3eac4f0700abe79b9be3e40688a4222d9b3c141a40475f1ea9'

def need(ok, message):
    if not ok:
        raise ValueError(message)

def load(path, digest):
    data = path.read_bytes()
    need(hashlib.sha256(data).hexdigest() == digest, 'source pin: ' + path.name)
    module = types.ModuleType('_review_' + path.stem)
    module.__file__ = str(path)
    exec(compile(data, str(path), 'exec'), module.__dict__)
    return module

def direct(helper, program, t, squared):
    h = helper
    p0 = h.add(h.scale(h.var('x'), 3), h.var('Z0'))
    product = h.const(1)
    appended = {}; bits = {}; boolean = []
    for i in range(t):
        d = h.add(h.var('D' + str(i)), h.const(-1))
        n = program[i % len(program)]
        appended = h.add(appended, h.scale(h.mul(d, product), 2 * (4**n - 1) // 3))
        product = h.mul(product, h.add(h.const(1), h.scale(d, 2 * 4**n - 1)))
        bits = h.add(bits, h.scale(d, 2**i))
        boolean.append(h.mul(d, h.add(d, h.const(-1))))
    r = h.add(h.mul(p0, product), h.const(-(2**t)))
    e = h.add(h.add(bits, h.var('x'), -1), h.mul(p0, appended), -1)
    output = h.add(h.mul(r, r), h.mul(e, e))
    for b in boolean:
        output = h.add(output, h.mul(b, b) if squared else b)
    return r, e, boolean, output

def value(poly, values):
    total = 0
    for term, coefficient in poly.items():
        for name in term:
            coefficient *= values[name]
        total += coefficient
    return total

def verify(source, root):
    m = load(source, SOURCE_PIN)
    h = load(root / 'review_grill_word_closure_independent.py', HELPER_PIN)
    parent = h.load(root / 'grill_tag_word_closure.py')
    count = Counter()
    programs = ((0,), (1,), (0, 1, 1), (1, 0), (2, 0, 1), (0, 0, 2, 1))
    for program, t, squared in itertools.product(programs, range(1, 7), (False, True)):
        p = m.build(program, t, square_boolean=squared, root=root)
        old = parent.build(program, t, square_boolean=squared)
        env, gates = h.formal(p)
        oldenv, _ = h.formal(old)
        r, e, boolean, output = direct(h, program, t, squared)
        expected_rows = [r, e] + boolean
        need(env[p['output']] == output, 'complete polynomial from direct product formula')
        need(all(env[n] == q for n, q in zip(p['residuals'], expected_rows)), 'every residual')
        need(oldenv[old['residuals'][1]] == h.add(r, h.scale(e, 3)), 'old content = r+3e')
        correction = h.add(h.add(h.mul(r, r), h.scale(h.mul(r, e), 6)), h.scale(h.mul(e, e), 8))
        need(h.add(oldenv[old['output']], output, -1) == correction, 'entire off-zero correction')
        degree = max(map(len, output))
        need(degree == 2*t+2, 'attained exact degree')
        z = sum(program[i % len(program)] == 0 for i in range(t))
        M = 5*t+2-2*z+t*squared; A = 6*t+3-z
        need(gates == dict(M=M, A=A), 'full live gate census')
        need(p['ledger'] == dict(operations=M+A, M=M, A=A, positive_witnesses=t+1, residuals=t+2, exact_degree=degree), 'full ledger')
        need(old['inputs'] == p['inputs'] and old['witnesses'] == p['witnesses'], 'identical coordinates')
        need(old['ledger']['operations'] - M - A == 2+2*z-t, 'signed operation difference')
        count['complete_expanded_sources'] += 1
        count['complete_polynomial_corrections'] += 1
        count['residual_identities'] += t+2
        for seed in range(3):
            values = {n: (seed+3*i) % 11-5 for i, n in enumerate(p['inputs']+p['witnesses'])}
            need(m.evaluate(p, values, signed=True, root=root) == value(output, values), 'signed public evaluator')
            count['signed_evaluations'] += 1
    census, fixtures = h.census(programs)
    count.update(census)
    for fixture, squared in itertools.product(fixtures, (False, True)):
        program = tuple(fixture['program']); t = fixture['t']
        p = m.build(program, t, square_boolean=squared, root=root)
        values = dict(x=fixture['x'], Z0=fixture['Z0'], **{'D'+str(i): d+1 for i, d in enumerate(fixture['heads'])})
        need(m.evaluate(p, values, root=root) == 0, 'every causal census zero')
        need(m.decode_zero(p, values, root=root)['actual_first_halt'] == fixture['halt'], 'independent actual halt')
        count['positive_zero_decodings'] += 1
    p = m.build((0,), 1, root=root)
    _, _, _, sparse = direct(h, (0,), 1, False)
    _, _, old = h.manual((0,), 1)
    for x, z in ((Fraction(1,2), Fraction(1,6)), (Fraction(1,3), Fraction(1,3))):
        v = dict(x=x, Z0=z, D0=Fraction(3,2))
        need((value(sparse, v) == 0) != (value(old, v) == 0), 'real zero sets differ in both directions')
        count['real_domain_separations'] += 1
    def reject(fn):
        try:
            fn()
        except (ValueError, TypeError, KeyError):
            count['malformed_rejected'] += 1
            return
        raise ValueError('malformed input accepted')
    for key in ('source', 'ledger', 'registers', 'residuals', 'witnesses', 'scope', 'parent', 'relation'):
        q = m.build((0,), 1, root=root); q[key] = None
        reject(lambda q=q: m.checked(q, root=root))
    for bad in ([], (), (True,), (-1,), (1.0,), None):
        reject(lambda bad=bad: m.build(bad, 1, root=root))
    for bad in (True, 0, -1, 1.0, None):
        reject(lambda bad=bad: m.build((0,), bad, root=root))
    for bad in (0, 1, None):
        reject(lambda bad=bad: m.build((0,), 1, square_boolean=bad, root=root))
    for name in ('x', 'Z0', 'D0'):
        for bad in (True, 1.0, 0, -1, None):
            v = dict(x=1, Z0=1, D0=2); v[name] = bad
            reject(lambda v=v: m.evaluate(p, v, root=root))
    reject(lambda: m.evaluate(p, dict(x=1, Z0=1, D0=2), signed=1, root=root))
    for field in ('source', 'registers', 'parent', 'relation'):
        q = m.build((0,), 1, root=root); q[field].clear()
        need(h.exact(p, m.build((0,), 1, root=root)), 'fresh defensive packet')
        count['defensive_copy_checks'] += 1
    return dict(status='PASS_INDEPENDENT_SPARSE_GRILL_CONTENT', source_sha256=SOURCE_PIN,
                helper_sha256=HELPER_PIN, review_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                counts=dict(count), scope='Same supplied integer zero set and positive input domain; different polynomial, different real zero sets. External horizon; no universality claim.')

if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source', type=Path, default=Path(__file__).with_name('grill_tag_sparse_content.py'))
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--expect', type=Path)
    args = ap.parse_args(); receipt = verify(args.source, args.root)
    if args.expect:
        need(receipt == json.loads(args.expect.read_text()), 'saved receipt')
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
    print(json.dumps(receipt, indent=2, sort_keys=True))
