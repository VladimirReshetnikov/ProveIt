#!/usr/bin/env python3
"""Reproduce the new finite checks; no Lean or TM equivalence claim.

Only Python's standard library is required. Output paths are explicit.
"""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import random
import time

import symbolic254 as lazy
import canonical254 as canon
from extract_specs import extract


def numeric_apply(name, args):
    """Independent direct arithmetic for the eight small logical rows.

    The large bundle is deliberately not expanded into a numeric integer.
    """
    p = lazy.pair
    im = lambda a, b: 4*p(a, b)
    el = lambda a, b: 4*p(a, b)+1
    al = lambda a, b: 4*p(a, b)+2
    eq = lambda a, b: 4*p(a, b)+3
    neg = lambda a: im(a, 1)
    ex = lambda a, b: neg(al(a, neg(b)))
    a, b, *rest = args
    c = rest[0] if rest else None
    if name == 'rho1': return ex(a, eq(a, b))
    if name == 'rho2': return im(al(a, im(b, c)), im(al(a, b), al(a, c)))
    if name == 'rho3': return im(eq(a, b), im(el(c, a), el(c, b)))
    if name == 'rho4': return im(al(a, al(b, c)), al(b, al(a, c)))
    if name == 'rho5': return im(eq(c, a), im(el(c, b), el(a, b)))
    if name == 'rho6': return im(ex(a, al(a, b)), b)
    if name == 'rho7': return im(eq(c, a), im(eq(c, b), eq(a, b)))
    if name == 'rho8':
        u = rest[1]
        return im(im(im(c, u), a), im(im(a, c), im(b, c)))
    raise ValueError(name)


def run(output, code_limit=50000, random_cases=3000):
    started = time.monotonic()
    rng = random.Random(25220261017)
    parsed = same_check = logical_values = 0
    counts = {str(t): 0 for t in range(12)}
    for code in range(code_limit):
        p = lazy.parse(code)
        if p is None:
            continue
        parsed += 1
        counts[str(p.tag)] += 1
        assert p.quote() == code
        size, height, product = p.measures()
        assert (1 << size) * product <= code + 1
        assert 1 << ((1 << height)-1) <= code + 1
        assert height <= (code.bit_length()+1).bit_length()-1
        # Distinct implementations of exact numeric formula equality.
        aa, bb = lazy.Arena(), canon.CanonicalArena()
        a, av, _ = lazy.build(p, aa)
        b, bv, _ = lazy.build(p, bb)
        assert av == bv
        n = code % 23
        assert (av and aa.equal(a, aa.literal(n))) == (bv and b == bb.literal(n))
        same_check += 1
        if 3 <= p.tag <= 10:
            expected = numeric_apply('rho'+str(p.tag-2), p.args)
            assert aa.equal(a, aa.literal(expected))
            assert b == bb.literal(expected)
            logical_values += 1
    # Canonical normal form and the positive-node mass inequality.
    aa = canon.CanonicalArena()
    all_ids = []
    mass_cache = {0: 0}
    def positive_nodes(n):
        if n not in mass_cache:
            a, b = lazy.unpair(n//4)
            mass_cache[n] = 1 + positive_nodes(a) + positive_nodes(b)
        return mass_cache[n]
    for n in range(20000):
        root = aa.literal(n)
        all_ids.append(root)
        assert aa.materialize(root) == n
        assert (1 << positive_nodes(n)) <= n+1
    assert len(set(all_ids)) == len(all_ids)
    assert aa.literal(0) != aa.b(0, aa.literal(1), aa.literal(1))
    # Random DAG operations against literal arithmetic; prevent unbounded QA output.
    roots = [(aa.literal(i), i) for i in range(16)]
    algebra = 0
    for _ in range(random_cases):
        x, a = rng.choice(roots)
        y, b = rng.choice(roots)
        tag = rng.randrange(4)
        n = 4*lazy.pair(a, b)+tag
        r = aa.b(tag, x, y)
        assert r == aa.literal(n)
        if n.bit_length() < 4096:
            roots.append((r, n))
        algebra += 1
    # Every logical axiom family plus actual GEN and MP certificates.
    specimens = [(lazy.Raw(0), 0)]
    for tag in range(3, 11):
        args = tuple(range(lazy.ARITY[tag]))
        p = lazy.Raw(tag, args)
        specimens.append((p, numeric_apply('rho'+str(tag-2), args)))
    p = lazy.Raw(0)
    n = 0
    for binder in (0, 1, 2, 0):
        p = lazy.Raw(2, (binder,), (p,))
        n = 4*lazy.pair(binder, n)+2
        specimens.append((p, n))
    specimens.extend([
        (lazy.Raw(1, (0,), (lazy.Raw(0), lazy.Raw(0))), 0),
        (lazy.Raw(1, (0,), (lazy.Raw(0), lazy.Raw(10, (0,0,0,0)))), 0)])
    certificates = []
    mutations = []
    for p, n in specimens:
        cert = canon.make_certificate(p, n)
        assert canon.verify_certificate(cert)
        assert cert['source_code'] == p.quote()
        assert canon.check(p.quote(), n)
        certificates.append(cert)
        bad = deepcopy(cert); bad['conclusion'] = n+1
        assert not canon.verify_certificate(bad); mutations.append('conclusion')
        bad = deepcopy(cert); bad['source_code'] += 1
        assert not canon.verify_certificate(bad); mutations.append('source-code')
        bad = deepcopy(cert); bad['proof_codes'][-1] += 1
        assert not canon.verify_certificate(bad); mutations.append('quote-row')
        bad = deepcopy(cert); bad['nodes'].append(['b',0,0,0])
        assert not canon.verify_certificate(bad); mutations.append('zero-alias')
        bad = deepcopy(cert); bad['nodes'].append(['b',1,len(bad['nodes']),0])
        assert not canon.verify_certificate(bad); mutations.append('cyclic-arena')
    bad = deepcopy(certificates[-1]); bad['proof_rows'][-1]['children'][0] = len(bad['proof_rows'])-1
    assert not canon.verify_certificate(bad); mutations.append('cyclic-proof')
    # Gated bundle construction and independently certified size interval.
    bundle = []
    for args in [(0,1,2),(0,1,0),(0,1,1),(2,2,3)]:
        p = lazy.Raw(11, args)
        aa, bb = lazy.Arena(), canon.CanonicalArena()
        a, av, _ = lazy.build(p, aa)
        b, bv, _ = lazy.build(p, bb)
        assert av == bv == (args[2] != args[0] and args[2] != args[1])
        assert aa.bit_bounds(a) == bb.bit_bounds(b)
        bundle.append({'args':list(args),'proof_quote':p.quote(),
                       'proof_quote_bits':p.quote().bit_length(),
                       'valid':bv,'canonical_nodes':len(bb.nodes),
                       'conclusion_bit_bounds':list(bb.bit_bounds(b))})
    # Certificate checker must not depend on inverse computations or producer.
    saved = canon.unpair, canon.parse, canon.build
    def forbidden(*args, **kwargs):
        raise AssertionError('Forbidden producer/inverse call')
    canon.unpair = canon.parse = canon.build = forbidden
    for cert in certificates:
        assert canon.verify_certificate(cert)
    canon.unpair, canon.parse, canon.build = saved
    output.mkdir(parents=True, exist_ok=True)
    (output/'example_certificate.json').write_text(json.dumps(certificates[1],indent=2)+'\n')
    (output/'example_mp_certificate.json').write_text(json.dumps(certificates[-1],indent=2)+'\n')
    result = {'source_pin':'fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
              'code_range':[0,code_limit], 'parsed_codes':parsed,
              'tag_counts':counts,'lazy_canonical_comparisons':same_check,
              'independent_numeric_axiom_values':logical_values,
              'literal_roundtrips':20000,'random_algebra_operations':algebra,
              'accepted_certificates':len(certificates),
              'corrupted_certificates_rejected':len(mutations),
              'inverse_free_verifier_checked':True,'bundle_examples':bundle,
              'seconds':round(time.monotonic()-started,3),
              'new_lean_proof':False,'new_binary_state_bound':False}
    (output/'sparse_certificate_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--output',type=Path,required=True)
    ap.add_argument('--code-limit',type=int,default=50000)
    ap.add_argument('--random-cases',type=int,default=3000)
    args = ap.parse_args()
    run(args.output,args.code_limit,args.random_cases)
