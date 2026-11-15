#!/usr/bin/env python3
"""Independently check a primitive-rule proof DAG without huge integers.

Each I-node denotes I_3(a,b)=3*Cantor(a,b).  The only numerical facts
used by the guard checker are reflexivity, natural-constant comparison,
and a,b <= I_3(a,b).  None of the source Lean proof text is trusted.
The proof certifies one nontrivial example; the uniform template and
primitive-recursive proof translation are established in recoding.tex.
"""
from pathlib import Path
import functools
import gzip
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
PATH = HERE / 'rho_guard_certificate.json.gz'
if not __debug__:
    raise RuntimeError('Use Python without -O')
cert = json.loads(gzip.decompress(PATH.read_bytes()))
assert cert['format'] == 'tagged3-rho8all-example-v1'
assert cert['coefficient'] == 3
terms = cert['terms']
rows = cert['proofs']
intern = {}
depth = []
for n, term in enumerate(terms):
    key = tuple(term)
    assert key not in intern, ('duplicate term', n)
    intern[key] = n
    if term[0] == 'nat':
        assert len(term) == 2 and isinstance(term[1], int) and term[1] >= 0
        depth.append(0)
    else:
        assert term[0] == 'I' and len(term) == 3
        assert 0 <= term[1] < n and 0 <= term[2] < n
        assert not (terms[term[1]] == ['nat', 0] == terms[term[2]])
        depth.append(1 + max(depth[term[1]], depth[term[2]]))
zero = intern[('nat', 0)]

def implication(a, b):
    return zero if a == b == zero else intern[('I', a, b)]

def rho(a, b, c, u):
    return implication(implication(implication(c, u), a),
                       implication(implication(a, c), implication(b, c)))

@functools.lru_cache(None)
def dominated(u, a):
    if u == a or u == zero:
        return True
    left, right = terms[u], terms[a]
    if left[0] == right[0] == 'nat':
        return left[1] <= right[1]
    if right[0] == 'I':
        return dominated(u, right[1]) or dominated(u, right[2])
    return False

counts = {'rho8': 0, 'mp': 0}
for n, row in enumerate(rows):
    conclusion = row['conclusion']
    assert 0 <= conclusion < len(terms)
    if row['rule'] == 'rho8':
        assert len(row['args']) == 4
        a, b, c, u = row['args']
        assert all(0 <= v < len(terms) for v in (a,b,c,u))
        assert dominated(u, a), ('unproved guard', n, a, u)
        assert conclusion == rho(a,b,c,u), ('rho formula',n)
    else:
        assert row['rule'] == 'mp' and len(row['args']) == 2
        major, minor = row['args']
        assert 0 <= major < n and 0 <= minor < n
        major_term = rows[major]['conclusion']
        minor_term = rows[minor]['conclusion']
        if major_term == zero:
            assert minor_term == conclusion == zero
        else:
            node = terms[major_term]
            assert node[0] == 'I' and node[1] == minor_term
            assert node[2] == conclusion
    counts[row['rule']] += 1

params = cert['parameters']
assert params == {'D':3,'A':0,'H':0,'u':7}
final = cert['final']
assert 0 <= final < len(rows)
assert rows[final]['conclusion'] == rho(intern[('nat',3)],zero,zero,intern[('nat',7)])
assert params['u'] > params['D']
summary = dict(status='PASS', coefficient=3, terms=len(terms),
               proof_rows=len(rows), primitive_rules=counts,
               largest_term_depth=max(depth), final_parameters=params,
               all_primitive_guards_verified=True,
               final_guard_directly_fails=True,
               certificate_sha256=hashlib.sha256(PATH.read_bytes()).hexdigest(),
               source_sha256=cert['source_sha256'],
               checker_scope='One expanded rho8All instance, not the universal theorem')
(HERE/'rho_guard_certificate_check.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
