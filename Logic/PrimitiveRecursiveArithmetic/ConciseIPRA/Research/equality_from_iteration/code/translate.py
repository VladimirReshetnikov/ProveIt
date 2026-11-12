"""Untrusted proof compilers for the two matched rule-deletion comparisons.

The checker modules remain standalone. This file is not imported by them.
Only the root-equality branch is expanded; all end-sequents are unchanged.
"""

import copy
import json
import sys

import checker as single
import normalized_control as normal
import raw_control as raw
import raw_two_case as two


def root_compose(p, q, s, normalized=False):
    """Given p:s=t and q:s=r, return a proof of r=t."""
    if normalized:
        bridge = ['i', ['s', ['z']], s, ['v', 0]]
    else:
        bridge = ['i', ['z'], s, ['z']]
    return ['ev', p, ['ev', q, ['refl', bridge]]]


def compile_proof(p, g, n, normalized=False):
    source = normal if normalized else raw
    tag = p[0]
    if tag in ('hyp', 'refl'):
        return copy.deepcopy(p)
    if tag == 'ev':
        _, s, _ = source.infer(p[1], g, n)
        _, b, _ = source.infer(p[2], g, n)
        left = compile_proof(p[1], g, n, normalized)
        right = compile_proof(p[2], g, n, normalized)
        if b == s:
            return root_compose(left, right, s, normalized)
        return ['ev', left, right]
    if tag == 'qe':
        return ['qe', copy.deepcopy(p[1]),
                compile_proof(p[2], g, n, normalized),
                compile_proof(p[3], g, n, normalized)]
    if tag == 'de':
        b = source.infer(p[2], g, n)
        local = [['q', b[1]]] + [source.shift(a) for a in g]
        return ['de', copy.deepcopy(p[1]),
                compile_proof(p[2], g, n, normalized),
                compile_proof(p[3], local, n + 1, normalized)]
    if tag == 'di':
        b, t = p[1:3]
        a = source.sub(['q', b], t)[1]
        h = a if a[0] == '=' and t == ['z'] else source.shift(source.sub(a, ['z']))
        local = [h] + [source.shift(a) for a in g]
        return ['di', copy.deepcopy(b), copy.deepcopy(t),
                compile_proof(p[3], local, n + 1, normalized)]
    raise ValueError('Invalid source proof')


def translate(certificate, normalized=False):
    source, target = (normal, single) if normalized else (raw, two)
    source.check(certificate)
    result = copy.deepcopy(certificate)
    result['proof'] = compile_proof(certificate['proof'], certificate['context'],
                                    certificate['variables'], normalized)
    target.check(result)
    return result


if __name__ == '__main__':
    result = translate(json.load(sys.stdin), '--normalized' in sys.argv[1:])
    json.dump(result, sys.stdout, separators=(',', ':'))
    print()
