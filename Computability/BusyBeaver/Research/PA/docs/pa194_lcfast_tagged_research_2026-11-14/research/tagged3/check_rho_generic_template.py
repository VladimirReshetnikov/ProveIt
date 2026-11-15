#!/usr/bin/env python3
"""Check a formal rho8All template independently of its source derivation.

Sound interpretation: assign arbitrary values to the four variables;
interpret I by any operation with a,b <= I(a,b).  Syntactic subtree
inclusion then proves every primitive rho guard.  Each MP equality is
literal syntactic equality, hence is preserved by every interpretation.
This is a finite universal proof template, not an input sampling test.
"""
from pathlib import Path
from functools import lru_cache
import gzip
import hashlib
import json

HERE = Path(__file__).resolve().parent
PATH = HERE/'rho_generic_template.json.gz'
if not __debug__:
    raise RuntimeError('Use Python without -O')
cert = json.loads(gzip.decompress(PATH.read_bytes()))
assert cert['format'] == 'generic-rho8all-template-v1'
terms, rows = cert['terms'], cert['proofs']
intern = {}
depth = []
for n, node in enumerate(terms):
    key = tuple(node)
    assert key not in intern
    intern[key] = n
    if node[0] == 'var':
        assert n < 4 and node == ['var',('D','A','H','u')[n]]
        depth.append(0)
    else:
        assert node[0] == 'I' and len(node) == 3
        assert 0 <= node[1] < n and 0 <= node[2] < n
        depth.append(1+max(depth[node[1]],depth[node[2]]))
assert terms[:4] == [['var',n] for n in ('D','A','H','u')]

def implication(a,b):
    return intern[('I',a,b)]

def rho(a,b,c,u):
    return implication(implication(implication(c,u),a),
                       implication(implication(a,c),implication(b,c)))

@lru_cache(None)
def subtree(u,a):
    if u == a:
        return True
    node = terms[a]
    return (node[0] == 'I' and
            (subtree(u,node[1]) or subtree(u,node[2])))

counts = {'rho8':0,'mp':0}
for n,row in enumerate(rows):
    conclusion = row['conclusion']
    assert 0 <= conclusion < len(terms)
    if row['rule'] == 'rho8':
        assert len(row['args']) == 4
        a,b,c,u = row['args']
        assert all(0 <= x < len(terms) for x in (a,b,c,u))
        assert subtree(u,a), ('guard is not a subtree bound',n,a,u)
        assert conclusion == rho(a,b,c,u)
    else:
        assert row['rule'] == 'mp' and len(row['args']) == 2
        major,minor = row['args']
        assert 0 <= major < n and 0 <= minor < n
        node = terms[rows[major]['conclusion']]
        assert node[0] == 'I'
        assert node[1] == rows[minor]['conclusion']
        assert node[2] == conclusion
    counts[row['rule']] += 1
final = cert['final']
assert 0 <= final < len(rows)
assert rows[final]['conclusion'] == rho(0,1,2,3)
summary = dict(status='PASS',terms=len(terms),proof_rows=len(rows),
               primitive_rules=counts,largest_term_depth=max(depth),
               every_primitive_guard_is_a_syntactic_subtree_bound=True,
               conclusion='rho(D,A,H,u) for four unrestricted formal variables',
               interpretation='Any implication operation with reflexivity and propagation of order through either child',
               certificate_sha256=hashlib.sha256(PATH.read_bytes()).hexdigest(),
               source_sha256=cert['source_sha256'],
               checker_scope='Complete finite formal proof template; no PA or physical TM endpoint checked')
(HERE/'rho_generic_template_check.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
