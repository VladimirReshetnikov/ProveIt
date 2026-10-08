"""Native compressed singleton-generator splitting for arbitrary strand counts.

The topological connected-sum split is established prior work in ProveIt.
This module performs the whole analysis and all projections on the input DAG.
No compressed leaf is expanded. More-than-three-strand unresolved leaves are
returned INCONCLUSIVE, never asserted unknotted.
"""
from copy import deepcopy
import json
from .engine import recognize
from .verify import verify as verify_three, require, InvalidCertificate


def summarize(data, *, check=lambda: None):
    check()
    require(isinstance(data, dict) and set(data) == {'strands', 'rules', 'root'}, 'invalid grammar object')
    m, rules, root = data['strands'], data['rules'], data['root']
    require(type(m) is int and m >= 1, 'invalid strand count')
    require(isinstance(rules, list) and rules and rules[0] == ['e'], 'missing empty rule')
    require(type(root) is int and 0 <= root < len(rules), 'invalid root')
    lengths, exponents = [0], [0]
    for i, rule in enumerate(rules[1:], 1):
        check()
        require(isinstance(rule, list) and bool(rule), 'invalid rule')
        if rule[0] == 'g' and len(rule) == 2:
            g = rule[1]
            require(type(g) is int and 1 <= abs(g) < m, 'invalid generator')
            lengths.append(1)
            exponents.append(1 if g > 0 else -1)
        elif rule[0] == 'c' and len(rule) == 3:
            u, v = rule[1:]
            require(all(type(x) is int and 0 <= x < i for x in (u, v)), 'invalid dependency')
            lengths.append(lengths[u] + lengths[v])
            exponents.append(exponents[u] + exponents[v])
        else:
            raise InvalidCertificate('invalid rule opcode')
    weights = [0] * len(rules)
    weights[root] = 1
    counts = {}
    for i in range(len(rules) - 1, 0, -1):
        check()
        rule, weight = rules[i], weights[i]
        if not weight:
            continue
        if rule[0] == 'g':
            label = abs(rule[1])
            counts[label] = counts.get(label, 0) + weight
        else:
            weights[rule[1]] += weight
            weights[rule[2]] += weight
    # Find a gap without iterating through a possibly enormous strand range.
    gap = 1
    for label in sorted(counts):
        check()
        if label == gap:
            gap += 1
        else:
            break
    if gap < m:
        return dict(length=lengths[root], exponent=exponents[root], counts=counts,
                    gap=gap, knot=False, permutation=None)
    # Complete support entails m <= number of terminal rules + 1.
    permutations = [tuple(range(m))]
    for rule in rules[1:]:
        check()
        if rule[0] == 'g':
            p = list(range(m))
            i = abs(rule[1]) - 1
            p[i], p[i + 1] = p[i + 1], p[i]
            permutations.append(tuple(p))
        else:
            p, q = permutations[rule[1]], permutations[rule[2]]
            permutations.append(tuple(p[q[i]] for i in range(m)))
    p = permutations[root]
    current, seen = 0, set()
    while current not in seen:
        check()
        seen.add(current)
        current = p[current]
    return dict(length=lengths[root], exponent=exponents[root], counts=counts,
                gap=None, knot=len(seen) == m, permutation=list(p))


def project(data, low, high, *, check=lambda: None):
    """Project to the consecutive strand interval [low, high], inclusively."""
    out, intern, mapped = [['e']], {}, [0]
    def add(rule):
        key = tuple(rule)
        if key not in intern:
            intern[key] = len(out)
            out.append(rule)
        return intern[key]
    for rule in data['rules'][1:]:
        check()
        if rule[0] == 'g':
            g = rule[1]
            value = (add(['g', (1 if g > 0 else -1) * (abs(g) - low + 1)])
                     if low <= abs(g) < high else 0)
        else:
            u, v = mapped[rule[1]], mapped[rule[2]]
            value = add(['c', u, v]) if u and v else (u or v)
        mapped.append(value)
    return dict(strands=high - low + 1, rules=out, root=mapped[data['root']])


def recognize_forest(data, **arena_options):
    check = arena_options.get('check', lambda: None)
    s = summarize(data, check=check)
    certificate = dict(version='compressed-singleton-forest-v1', input=deepcopy(data))
    if not s['knot']:
        certificate.update(status='LINK', phase='components', gap=s['gap'], permutation=s['permutation'])
        return dict(status='LINK', certificate=certificate)
    cuts = sorted(i for i, count in s['counts'].items() if count == 1)
    boundaries = [0] + cuts + [data['strands']]
    leaves = []
    for lo, hi in zip(boundaries, boundaries[1:]):
        check()
        leaf = project(data, lo + 1, hi, check=check)
        m = leaf['strands']
        ls = summarize(leaf, check=check)
        if not ls['knot']:
            raise RuntimeError('singleton split of a knot produced a link')
        if m <= 2:
            status = 'UNKNOT' if m == 1 or abs(ls['exponent']) == 1 else 'KNOTTED'
            child = dict(version='at-most-two-v1', exponent_hex=hex(ls['exponent']), status=status)
        elif m == 3:
            result = recognize(leaf, **arena_options)
            status, child = result['status'], result['certificate']
        elif abs(ls['exponent']) > m - 1:
            status = 'KNOTTED'
            child = dict(version='bennequin-v1', exponent_hex=hex(ls['exponent']), status=status)
        else:
            status, child = 'INCONCLUSIVE', None
        leaves.append(dict(low=lo + 1, high=hi, grammar=leaf, status=status,
                           certificate=child, length_hex=hex(ls['length'])))
    statuses = [leaf['status'] for leaf in leaves]
    status = ('KNOTTED' if 'KNOTTED' in statuses else
              'UNKNOT' if all(x == 'UNKNOT' for x in statuses) else 'INCONCLUSIVE')
    certificate.update(phase='split', status=status, cuts=cuts, leaves=leaves)
    return dict(status=status, certificate=certificate)


def verify_forest(data, certificate, **arena_options):
    check = arena_options.get('check', lambda: None)
    c, s = certificate, summarize(data, check=check)
    require(isinstance(c, dict) and c.get('version') == 'compressed-singleton-forest-v1', 'wrong version')
    require(json.dumps(c.get('input'), sort_keys=True, separators=(',', ':')) ==
            json.dumps(data, sort_keys=True, separators=(',', ':')), 'wrong source grammar')
    if c.get('phase') == 'components':
        require(not s['knot'] and c.get('status') == 'LINK', 'invalid link verdict')
        require(json.dumps([c.get('gap'), c.get('permutation')]) ==
                json.dumps([s['gap'], s['permutation']]), 'wrong component witness')
        return 'LINK'
    require(c.get('phase') == 'split' and s['knot'], 'invalid split phase')
    cuts = sorted(i for i, count in s['counts'].items() if count == 1)
    require(isinstance(c.get('cuts'), list) and all(type(v) is int for v in c['cuts'])
            and c['cuts'] == cuts, 'inexact singleton cuts')
    boundaries = [0] + cuts + [data['strands']]
    leaves = c.get('leaves')
    require(isinstance(leaves, list) and len(leaves) == len(boundaries) - 1, 'wrong leaf count')
    statuses = []
    for item, (lo, hi) in zip(leaves, zip(boundaries, boundaries[1:])):
        check()
        require(isinstance(item, dict), 'invalid leaf record')
        require(type(item.get('low')) is int and type(item.get('high')) is int
                and item['low'] == lo + 1 and item['high'] == hi, 'wrong strand interval')
        leaf = project(data, lo + 1, hi, check=check)
        require(json.dumps(item.get('grammar'), sort_keys=True, separators=(',', ':')) ==
                json.dumps(leaf, sort_keys=True, separators=(',', ':')),
                'projected grammar differs from source projection')
        ls = summarize(leaf, check=check)
        require(ls['knot'] and item.get('length_hex') == hex(ls['length']), 'wrong leaf metadata')
        m, child = leaf['strands'], item.get('certificate')
        if m <= 2:
            status = 'UNKNOT' if m == 1 or abs(ls['exponent']) == 1 else 'KNOTTED'
            require(child == dict(version='at-most-two-v1', exponent_hex=hex(ls['exponent']), status=status),
                    'invalid two-strand certificate')
        elif m == 3:
            status = verify_three(leaf, child, **arena_options)
        elif abs(ls['exponent']) > m - 1:
            status = 'KNOTTED'
            require(child == dict(version='bennequin-v1', exponent_hex=hex(ls['exponent']), status=status),
                    'invalid Bennequin certificate')
        else:
            status = 'INCONCLUSIVE'
            require(child is None, 'unsupported leaf assertion')
        require(item.get('status') == status, 'wrong leaf verdict')
        statuses.append(status)
    status = ('KNOTTED' if 'KNOTTED' in statuses else
              'UNKNOT' if all(x == 'UNKNOT' for x in statuses) else 'INCONCLUSIVE')
    require(c.get('status') == status, 'incorrect connected-sum verdict')
    return status
