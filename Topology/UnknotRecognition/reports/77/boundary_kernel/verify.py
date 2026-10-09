"""Independent dense-matrix replay of finite boundary-word certificates.

This verifier does not call the producer's group law, power, or evaluation.
It verifies algebra only, never embeddedness, simplicity, or an unknot verdict.
"""
from __future__ import annotations
import hashlib
import json


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def multiply(a, b, q):
    n = len(a)
    return [[sum(a[i][h]*b[h][j] for h in range(n)) % q
             for j in range(n)] for i in range(n)]


def inverse(a, q):
    n = len(a)
    delta = [[(a[i][j]-int(i == j)) % q for j in range(n)] for i in range(n)]
    square = multiply(delta, delta, q)
    return [[(int(i == j)-delta[i][j]+square[i][j]) % q
             for j in range(n)] for i in range(n)]


def power(a, exponent, q):
    # Matrices are unipotent of nilpotence class two. Their exponent divides 2q.
    if type(exponent) is int:
        exponent = ('-' if exponent < 0 else '')+'0b'+format(abs(exponent), 'b')
    if not isinstance(exponent, str):
        raise ValueError('invalid exponent')
    negative = exponent.startswith('-')
    s = exponent[1:] if exponent.startswith(('-', '+')) else exponent
    if not s.startswith('0b') or len(s) < 3 or any(x not in '01' for x in s[2:]):
        raise ValueError('invalid binary exponent')
    r = 0
    for x in s[2:]: r = (2*r+int(x)) % (2*q)
    if negative: r = -r % (2*q)
    out = identity(len(a))
    while r:
        if r & 1: out = multiply(out, a, q)
        a = multiply(a, a, q)
        r >>= 1
    return out


def replay(word, g, q):
    if type(g) is not int or g < 2 or type(q) is not int or q not in (g, 2*g):
        raise ValueError('unsupported surface/modulus')
    if not isinstance(word, dict) or set(word) != {'rules','root'}:
        raise ValueError('malformed word')
    rules, root = word['rules'], word['root']
    if not isinstance(rules, list) or not rules or type(root) is not int or not 0 <= root < len(rules):
        raise ValueError('malformed root')
    n, values = g+2, []
    for i, r in enumerate(rules):
        if not isinstance(r, list) or not r: raise ValueError('malformed rule')
        op = r[0]
        if op not in ('id','gen','cat','inv','pow'): raise ValueError('unknown operation')
        if len(r) != {'id':1,'gen':2,'cat':3,'inv':2,'pow':3}[op]: raise ValueError('arity')
        refs = r[1:] if op == 'cat' else r[1:2] if op in ('inv','pow') else []
        if any(type(j) is not int or not 0 <= j < i for j in refs): raise ValueError('forward reference')
        if op == 'id': m = identity(n)
        elif op == 'gen':
            if type(r[1]) is not int or not 1 <= abs(r[1]) <= 2*g: raise ValueError('letter')
            j = abs(r[1])-1
            m = identity(n)
            if j % 2: m[1+j//2][-1] = (1 if r[1] > 0 else -1) % q
            else: m[0][1+j//2] = (1 if r[1] > 0 else -1) % q
        elif op == 'cat': m = multiply(values[r[1]], values[r[2]], q)
        elif op == 'inv': m = inverse(values[r[1]], q)
        else: m = power(values[r[1]], r[2], q)
        values.append(m)
    m = values[root]
    v = []
    for i in range(g): v.extend((m[0][1+i], m[1+i][-1]))
    return v, m[0][-1] % g


def verify_certificate(cert):
    """Return False for any inconsistent record; no source-geometry certification."""
    try:
        if cert['schema'] != 'boundary-heisenberg-observation-v1': return False
        g, q, word = cert['genus'], cert['coordinate_modulus'], cert['word']
        if q != g and not (g % 2 == 0 and q == 2*g): return False
        digest = hashlib.sha256(json.dumps(word, sort_keys=True, separators=(',',':')).encode()).hexdigest()
        if cert['word_sha256'] != digest: return False
        vector, area = replay(word, g, q)
        if cert['vector'] != vector or cert['area'] != area: return False
        if type(cert['area']) is not int or any(type(x) is not int for x in cert['vector']): return False
        nonsep, positive = any(vector), any(vector) or area != 0
        status = 'NONTRIVIAL' if positive else 'UNDETECTED'
        consequence = 'essential nonseparating' if nonsep else 'essential separating' if area else 'contractible'
        genera = None if nonsep else sorted((area,g-area))
        return (cert['status'] == status and cert['simple_curve_consequence'] == consequence
                and cert['complementary_genera_if_simple'] == genera
                and cert['requires_external_simple_source_for_consequence'] is True)
    except (KeyError, TypeError, ValueError, IndexError, OverflowError):
        return False
