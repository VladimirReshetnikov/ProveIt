#!/usr/bin/env python3
"""Check the inherited dominated certificate using constructor laws only.

No numerical Cantor formula occurs in the proof checker.  Consequently a
PASS certifies that its proof steps and bounds use only I(0,0)=0 and
domination of both arguments.  See constructor_orientation.md for the
all-natural interpretation and the exact code-isomorphism theorem.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT = HERE.parent / 'reference/dominated_rho8_full_certificate.json'


def check(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    assert data['format'] == 'term_dag_v1'
    nodes = [('truth',)]
    interned = {nodes[0]: 0}

    def intern(node):
        if node not in interned:
            interned[node] = len(nodes)
            nodes.append(node)
        return interned[node]

    def var(v):
        assert type(v) is int and v >= 0
        return intern(('var', v))

    def imp(a, b):
        return 0 if a == b == 0 else intern(('imp', a, b))

    def split(t):
        if t == 0:
            return 0, 0
        row = nodes[t]
        assert row[0] == 'imp'
        return row[1], row[2]

    terms = []
    for x in data['term_table']:
        if x == 'T':
            t = 0
        elif isinstance(x, dict):
            assert set(x) == {'var'}
            t = var(x['var'])
        else:
            assert isinstance(x, list) and len(x) == 2
            assert all(type(k) is int and 0 <= k < len(terms) for k in x)
            t = imp(terms[x[0]], terms[x[1]])
        terms.append(t)

    @lru_cache(None)
    def subterm_depth(a, u):
        if a == u:
            return 0
        row = nodes[a]
        if row[0] != 'imp':
            return None
        depths = [subterm_depth(x, u) for x in row[1:]]
        depths = [x + 1 for x in depths if x is not None]
        return min(depths) if depths else None

    def substitute(t, encoded_env):
        env = {int(k): terms[v] for k, v in encoded_env.items()}
        assert len(env) == len(encoded_env)

        @lru_cache(None)
        def go(t):
            row = nodes[t]
            if row[0] == 'truth':
                return 0
            if row[0] == 'var':
                assert row[1] in env
                return env[row[1]]
            return imp(go(row[1]), go(row[2]))

        return go(t)

    def alpha_equal(source, target):
        """A bijective renaming of universally quantified schema variables."""
        forward, backward, visited = {}, {}, set()
        work = [(source, target)]
        while work:
            s, t = work.pop()
            if (s, t) in visited:
                continue
            visited.add((s, t))
            left, right = nodes[s], nodes[t]
            assert left[0] == right[0]
            if left[0] == 'var':
                a, b = left[1], right[1]
                assert forward.get(a, b) == b and backward.get(b, a) == a
                forward[a], backward[b] = b, a
            elif left[0] == 'imp':
                work.extend(zip(left[1:], right[1:]))
            else:
                assert s == t == 0

    checked, counts, bound_counts = [], Counter(), Counter()
    for step in data['nodes']:
        assert step['id'] == len(checked)
        t, rule = terms[step['term']], step['rule']
        kind = rule['kind']
        counts[kind] += 1

        def previous(k):
            assert type(k) is int and 0 <= k < len(checked)
            return checked[k]

        if kind == 'truth':
            assert t == 0
        elif kind == 'dominated_rho8':
            left, right = split(t)
            cu, a = split(left)
            c, u = split(cu)
            ac, bc = split(right)
            aa, cc = split(ac)
            b, ccc = split(bc)
            assert a == aa and c == cc == ccc
            # Reconstruct, including the unique permitted zero rewrite.
            assert t == imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))
            if u == 0:
                bound_counts['zero'] += 1
            else:
                depth = subterm_depth(a, u)
                assert depth is not None
                bound_counts['subterm_depth_' + str(depth)] += 1
        elif kind == 'substitution':
            assert t == substitute(previous(rule['parent']), rule['substitution'])
        elif kind in ('mp', 'mp_substitution'):
            major, minor = previous(rule['major']), previous(rule['minor'])
            if kind == 'mp_substitution':
                major = substitute(major, rule['major_substitution'])
                minor = substitute(minor, rule['minor_substitution'])
            antecedent, consequent = split(major)
            assert antecedent == minor
            if kind == 'mp_substitution':
                alpha_equal(consequent, t)
            else:
                assert consequent == t
        else:
            raise AssertionError('Unsupported rule: ' + kind)
        checked.append(t)

    a, b, c, u = [var(i) for i in range(4)]
    expected = {
        'I': imp(a, a),
        'K': imp(a, imp(b, a)),
        'P': imp(imp(imp(a, b), a), a),
        'B': imp(imp(a, b), imp(imp(b, c), imp(a, c))),
        'S': imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c))),
        'rho8': imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c))),
    }
    for name, t in expected.items():
        assert checked[data['roots'][name]] == t
    assert bound_counts == Counter({'zero': 224, 'subterm_depth_0': 164,
                                   'subterm_depth_1': 755, 'subterm_depth_2': 112,
                                   'subterm_depth_3': 3, 'subterm_depth_4': 2})
    return {
        'status': 'PASS',
        'certificate_sha256': hashlib.sha256(raw).hexdigest(),
        'proof_nodes': len(checked),
        'input_term_nodes': len(terms),
        'rule_counts': dict(counts),
        'bound_witness_counts': dict(bound_counts),
        'checked_roots': list(expected),
        'constructor_requirements': ['I(0,0)=0', 'I(a,b)>=a', 'I(a,b)>=b'],
        'uses_cantor_arithmetic_in_proof_checker': False,
        'scope': 'Generic finite certificate audit. The all-natural transport and orientation theorems are proved in constructor_orientation.md.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate', type=Path, default=DEFAULT)
    parser.add_argument('--output', type=Path, default=HERE / 'orientation_certificate_receipt.json')
    args = parser.parse_args()
    receipt = check(args.certificate)
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
