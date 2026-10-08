"""Native compressed singleton-generator splitting for arbitrary strand counts.

The topological connected-sum split is established prior work in ProveIt.
This module performs the whole analysis and all projections on the input DAG.
Three-strand leaves are never expanded. An optional bounded exact cube handles
wider exceptional leaves; legacy proofs retain their inconclusive semantics.
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
    check()
    if low == high:
        # Every generator is erased. This is exactly the old canonical output,
        # including when unreachable rules are present in the validated input.
        return dict(strands=1, rules=[['e']], root=0)
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


def _factor_plan(data, summary, intervals, check):
    """Exact projected lengths/exponents and a cheap rule-count upper bound.

    A node's nonempty factor projections lie within the hull of its terminal
    factor indices. Range additions count all such hulls in linear space.
    The bound need not be tight; it schedules work but proves no knot verdict.
    Caller has validated the full grammar and established a knot closure.
    """
    rules, count = data['rules'], len(intervals)
    labels = [-1] * data['strands']
    lengths, exponents = [0] * count, [0] * count
    for index, (lo, hi) in enumerate(intervals):
        check()
        for label in range(lo + 1, hi):
            check()
            labels[label] = index
            lengths[index] += summary['counts'][label]
    weights = [0] * len(rules)
    weights[data['root']] = 1
    for node in range(len(rules) - 1, 0, -1):
        check()
        rule, weight = rules[node], weights[node]
        if not weight:
            continue
        if rule[0] == 'g':
            index = labels[abs(rule[1])]
            if index >= 0:
                exponents[index] += weight if rule[1] > 0 else -weight
        else:
            weights[rule[1]] += weight
            weights[rule[2]] += weight
    spans, difference = [None], [0] * (count + 1)
    for rule in rules[1:]:
        check()
        if rule[0] == 'g':
            index = labels[abs(rule[1])]
            span = (index, index) if index >= 0 else None
        else:
            a, b = spans[rule[1]], spans[rule[2]]
            span = ((min(a[0], b[0]), max(a[1], b[1])) if a and b else a or b)
        spans.append(span)
        if span is not None:
            difference[span[0]] += 1
            difference[span[1] + 1] -= 1
    plan, covered = [], 0
    for index, (lo, hi) in enumerate(intervals):
        check()
        covered += difference[index]
        m, exponent = hi - lo, exponents[index]
        priority = 0 if m <= 2 or abs(exponent) > m - 1 else 1 if m == 3 else 2
        plan.append((priority, covered + 1, index, lo, hi, lengths[index], exponent))
    return sorted(plan)


def recognize_forest(data, *, fallback_max_crossings=0, fallback_reserve=lambda size: None,
                     use_fallback_reduction=True, use_lazy_factors=True, **arena_options):
    if type(use_lazy_factors) is not bool:
        raise ValueError('use_lazy_factors must be Boolean')
    check = arena_options.get('check', lambda: None)
    s = summarize(data, check=check)
    certificate = dict(version='compressed-singleton-forest-v1', input=deepcopy(data))
    if not s['knot']:
        certificate.update(status='LINK', phase='components', gap=s['gap'], permutation=s['permutation'])
        return dict(status='LINK', certificate=certificate)
    cuts = sorted(i for i, count in s['counts'].items() if count == 1)
    boundaries = [0] + cuts + [data['strands']]
    intervals = list(zip(boundaries, boundaries[1:]))
    def prepare():
        if use_lazy_factors:
            if len(intervals) == 1:
                lo, hi = intervals[0]
                plan = [(0, 0, 0, lo, hi, s['length'], s['exponent'])]
            else:
                plan = _factor_plan(data, s, intervals, check)
            for _, _, index, lo, hi, length, exponent in plan:
                check()
                leaf = project(data, lo + 1, hi, check=check)
                ls = summarize(leaf, check=check)
                if (ls['length'], ls['exponent']) != (length, exponent):
                    raise ArithmeticError('projected factor metadata differs from scheduling summary')
                yield index, lo, hi, leaf, ls
        else:
            prepared = []
            for index, (lo, hi) in enumerate(intervals):
                check()
                leaf = project(data, lo + 1, hi, check=check)
                ls = summarize(leaf, check=check)
                m = leaf['strands']
                priority = 0 if m <= 2 or abs(ls['exponent']) > m-1 else 1 if m == 3 else 2
                prepared.append((priority, len(leaf['rules']), index, lo, hi, leaf, ls))
            for _, _, index, lo, hi, leaf, ls in sorted(prepared):
                yield index, lo, hi, leaf, ls
    leaves, order = [None] * len(intervals), []
    for index, lo, hi, leaf, ls in prepare():
        check()
        if not ls['knot']:
            raise RuntimeError('singleton split of a knot produced a link')
        order.append(index)
        m = leaf['strands']
        if m <= 2:
            status = 'UNKNOT' if m == 1 or abs(ls['exponent']) == 1 else 'KNOTTED'
            child = dict(version='at-most-two-v1', exponent_hex=hex(ls['exponent']), status=status)
        elif m == 3:
            result = recognize(leaf, **arena_options)
            status, child = result['status'], result['certificate']
        elif abs(ls['exponent']) > m - 1:
            status = 'KNOTTED'
            child = dict(version='bennequin-v1', exponent_hex=hex(ls['exponent']), status=status)
        elif ls['length'] <= fallback_max_crossings:
            if use_fallback_reduction:
                from .exceptional import produce
                child = produce(leaf, ls, max_crossings=fallback_max_crossings,
                                reserve=fallback_reserve, **arena_options)
            else:
                from .cube import produce
                child = produce(leaf, ls, max_crossings=fallback_max_crossings,
                                check=check, reserve=fallback_reserve)
            status = child['status']
            if child['version'] == 'exceptional-reduction-v1':
                certificate['version'] = 'compressed-singleton-forest-v3'
            elif certificate['version'] != 'compressed-singleton-forest-v3':
                certificate['version'] = 'compressed-singleton-forest-v2'
        else:
            status, child = 'INCONCLUSIVE', None
        item = dict(low=lo + 1, high=hi, grammar=leaf, status=status,
                    certificate=child, length_hex=hex(ls['length']))
        if status == 'KNOTTED':
            # One nontrivial summand proves the whole knot nontrivial. Discard
            # earlier trivial or unsupported factors; their proofs are not needed.
            certificate.update(version='compressed-singleton-forest-v3',
                               phase='knotted-factor', status='KNOTTED', cuts=cuts,
                               factor_index=index, leaves=[item])
            return dict(status='KNOTTED', certificate=certificate, factor_order=order)
        leaves[index] = item
    status = 'UNKNOT' if all(leaf['status'] == 'UNKNOT' for leaf in leaves) else 'INCONCLUSIVE'
    certificate.update(phase='split', status=status, cuts=cuts, leaves=leaves)
    return dict(status=status, certificate=certificate, factor_order=order)


def verify_forest(data, certificate, *, fallback_max_crossings=0,
                  fallback_reserve=lambda size: None, **arena_options):
    check = arena_options.get('check', lambda: None)
    c, s = certificate, summarize(data, check=check)
    require(isinstance(c, dict) and c.get('version') in
            ('compressed-singleton-forest-v1', 'compressed-singleton-forest-v2',
             'compressed-singleton-forest-v3'), 'wrong version')
    require(json.dumps(c.get('input'), sort_keys=True, separators=(',', ':')) ==
            json.dumps(data, sort_keys=True, separators=(',', ':')), 'wrong source grammar')
    if c.get('phase') == 'components':
        require(not s['knot'] and c.get('status') == 'LINK', 'invalid link verdict')
        require(json.dumps([c.get('gap'), c.get('permutation')]) ==
                json.dumps([s['gap'], s['permutation']]), 'wrong component witness')
        return 'LINK'
    selected = c.get('phase') == 'knotted-factor'
    require(s['knot'] and (c.get('phase') == 'split' or
            selected and c['version'] == 'compressed-singleton-forest-v3'), 'invalid split phase')
    cuts = sorted(i for i, count in s['counts'].items() if count == 1)
    require(isinstance(c.get('cuts'), list) and all(type(v) is int for v in c['cuts'])
            and c['cuts'] == cuts, 'inexact singleton cuts')
    boundaries = [0] + cuts + [data['strands']]
    intervals = list(zip(boundaries, boundaries[1:]))
    if selected:
        index = c.get('factor_index')
        require(type(index) is int and 0 <= index < len(intervals), 'invalid selected factor')
        intervals = [intervals[index]]
    leaves = c.get('leaves')
    require(isinstance(leaves, list) and len(leaves) == len(intervals), 'wrong leaf count')
    statuses = []
    for item, (lo, hi) in zip(leaves, intervals):
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
        elif child is not None and c['version'] in ('compressed-singleton-forest-v2',
                                                   'compressed-singleton-forest-v3'):
            if isinstance(child, dict) and child.get('version') == 'exceptional-reduction-v1':
                require(c['version'] == 'compressed-singleton-forest-v3', 'reduction requires v3')
                from .exceptional import verify
                status = verify(leaf, ls, child, max_crossings=fallback_max_crossings,
                                reserve=fallback_reserve, **arena_options)
            else:
                from .cube_verify import verify
                status = verify(leaf, ls, child, max_crossings=fallback_max_crossings,
                                check=check, reserve=fallback_reserve)
        else:
            status = 'INCONCLUSIVE'
            require(child is None, 'unsupported leaf assertion')
        require(item.get('status') == status, 'wrong leaf verdict')
        statuses.append(status)
    if selected:
        require(statuses == ['KNOTTED'] and c.get('status') == 'KNOTTED',
                'selected factor must prove nontriviality')
        return 'KNOTTED'
    status = ('KNOTTED' if 'KNOTTED' in statuses else
              'UNKNOT' if all(x == 'UNKNOT' for x in statuses) else 'INCONCLUSIVE')
    require(c.get('status') == status, 'incorrect connected-sum verdict')
    return status
