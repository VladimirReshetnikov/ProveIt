"""Six-state max-plus powers for supplied repeat-safe alternating paths.

A summary/certificate is symbolic. It does not contain an expanded matching or
assert that a native three-dimensional input admits this repeat template.
"""
from __future__ import annotations
from .core import _nat

STATES = tuple((selected, direction) for selected in (0, 1) for direction in (-1, 0, 1))
INDEX = {state: i for i, state in enumerate(STATES)}


def identity():
    return [[0 if i == j else None for j in range(6)] for i in range(6)]


def multiply(a, b):
    c = [[None] * 6 for _ in range(6)]
    for i in range(6):
        for k in range(6):
            if a[i][k] is None: continue
            for j in range(6):
                if b[k][j] is None: continue
                value = a[i][k] + b[k][j]
                if c[i][j] is None or value > c[i][j]: c[i][j] = value
    return c


def transition(left_is_row, eligible, weight, occupied, free):
    matrix = [[None] * 6 for _ in range(6)]
    for i, (previous, direction) in enumerate(STATES):
        for selected in (0, 1):
            if previous + selected > 1 or (selected and not eligible): continue
            orient = (1 if selected else -1) if left_is_row else (-1 if selected else 1)
            newdir = direction if direction == orient else 0
            j = INDEX[selected, newdir]
            value = selected * weight + (occupied if previous or selected else free)
            if matrix[i][j] is None or value > matrix[i][j]: matrix[i][j] = value
    return matrix


def _validate_parameters(length, weight, first_is_row, eligibility, potentials):
    _nat(length, 'path length'); _nat(weight, 'row weight')
    if length < 1: raise ValueError('path length must be positive')
    if type(first_is_row) is not bool: raise ValueError('first_is_row must be bool')
    if len(eligibility) != 2 or any(type(x) is not bool for x in eligibility):
        raise ValueError('eligibility must be two booleans')
    if len(potentials) != 2 or any(len(pair) != 2 for pair in potentials):
        raise ValueError('potentials must give occupied/free scores for row and column')
    for occupied, free in potentials:
        _nat(occupied, 'occupied score'); _nat(free, 'free score')
        if occupied > free: raise ValueError('a free vertex cannot have a smaller optimum')


def periodic_path_table(length, *, weight=1, first_is_row=True,
                        eligibility=(True, True), potentials=((0, 0), (0, 0)),
                        certificate=False):
    """Exact table for an alternating length-L path with fresh internal vertices.

    Edge eligibility alternates; all row weights equal `weight`. The two
    vertex types have fixed occupied/free descendant scores. Endpoint scores
    are excluded. Products certify all states, not just one feasible score.
    """
    _validate_parameters(length, weight, first_is_row, eligibility, potentials)
    first_internal_is_row = not first_is_row
    a_pot = potentials[0 if first_internal_is_row else 1]
    b_pot = potentials[0 if first_is_row else 1]
    a = transition(first_internal_is_row, eligibility[1], weight, *a_pot)
    b = transition(first_is_row, eligibility[0], weight, *b_pot)
    nodes = [dict(kind='identity', matrix=identity()),
             dict(kind='transition', which='A', matrix=a),
             dict(kind='transition', which='B', matrix=b)]
    products = 0
    def product(i, j):
        nonlocal products
        products += 1
        nodes.append(dict(kind='product', left=i, right=j,
                          matrix=multiply(nodes[i]['matrix'], nodes[j]['matrix'])))
        return len(nodes) - 1
    pair = product(1, 2)
    exponent, tail = divmod(length - 1, 2)
    exponent_bits = exponent
    acc, base = 0, pair
    while exponent_bits:
        if exponent_bits & 1: acc = product(acc, base)
        exponent_bits >>= 1
        if exponent_bits: base = product(base, base)
    if tail: acc = product(acc, 1)
    total = nodes[acc]['matrix']
    table = {}
    for first in (0, 1):
        if first and not eligibility[0]: continue
        orient = (1 if first else -1) if first_is_row else (-1 if first else 1)
        i = INDEX[first, orient]
        for j, (last, direction) in enumerate(STATES):
            if total[i][j] is not None:
                table[first, last, direction] = first * weight + total[i][j]
    if len(table) > 6: raise ArithmeticError('six-state invariant failed')
    result = dict(schema='periodic-path-summary-v1', length=length,
                  table=[dict(first=a0, last=b0, direction=d, score=s)
                         for (a0, b0, d), s in sorted(table.items())],
                  matrix_products=products)
    if certificate:
        result['certificate'] = dict(schema='six-state-power-proof-v1',
            parameters=dict(length=length, weight=weight, first_is_row=first_is_row,
                            eligibility=list(eligibility), potentials=[list(x) for x in potentials]),
            nodes=nodes, output_node=acc, table=result['table'])
    return result


def periodic_cycle_optimum(half_length, *, weight=1, certificate=False):
    _nat(half_length, 'cycle half length')
    if half_length < 2: raise ValueError('a simple bipartite cycle has at least four edges')
    result = periodic_path_table(2 * half_length, weight=weight, certificate=certificate)
    valid = [entry['score'] for entry in result['table']
             if entry['first'] + entry['last'] <= 1 and entry['direction'] == 0]
    result.update(status='OPTIMAL_SYMBOLIC_CYCLE_SCORE', matched_weight=max(valid),
                  deferred_weight=half_length * weight - max(valid))
    return result


def verify_power_certificate(cert, *, max_nodes=100_000) -> bool:
    """Independent all-candidate replay of each matrix product and its type word.

    No call to the producer or its matrix multiplication is made. Bounds are
    admission guards, not source-geometry validation or a hardened parser.
    """
    try:
        if cert['schema'] != 'six-state-power-proof-v1': return False
        p = cert['parameters']
        length, weight = p['length'], p['weight']
        first_is_row, eligible, potentials = p['first_is_row'], p['eligibility'], p['potentials']
        _validate_parameters(length, weight, first_is_row, eligible, potentials)
        nodes = cert['nodes']
        if type(nodes) is not list or not 3 <= len(nodes) <= max_nodes: return False
        # Word summaries are (length, starting-letter, ending-letter) for an
        # alternating A/B word. They prevent replacing the requested exponent.
        words = []
        for k, node in enumerate(nodes):
            matrix = node['matrix']
            if type(matrix) is not list or len(matrix) != 6: return False
            for row in matrix:
                if type(row) is not list or len(row) != 6: return False
                if any(x is not None and type(x) is not int for x in row): return False
            kind = node['kind']
            if kind == 'identity':
                if k != 0: return False
                expected = [[0 if i == j else None for j in range(6)] for i in range(6)]
                word = (0, '', '')
            elif kind == 'transition':
                name = node['which']
                if (k, name) not in ((1, 'A'), (2, 'B')): return False
                isrow = not first_is_row if name == 'A' else first_is_row
                can_select = eligible[1 if name == 'A' else 0]
                occupied, free = potentials[0 if isrow else 1]
                expected = [[None] * 6 for _ in range(6)]
                # State-pair relation, rather than the producer's edge loop.
                for i, (old, old_d) in enumerate(STATES):
                    for j, (new, new_d) in enumerate(STATES):
                        if old + new > 1 or (new == 1 and not can_select): continue
                        forward = (new == 1) == isrow
                        orient = 1 if forward else -1
                        resulting = old_d if old_d == orient else 0
                        if resulting == new_d:
                            expected[i][j] = new * weight + (occupied if old + new else free)
                word = (1, name, name)
            elif kind == 'product':
                a, b = node['left'], node['right']
                if type(a) is not int or type(b) is not int or not 0 <= a < k or not 0 <= b < k:
                    return False
                expected = []
                for i in range(6):
                    row = []
                    for j in range(6):
                        candidates = [nodes[a]['matrix'][i][h] + nodes[b]['matrix'][h][j]
                                      for h in range(6)
                                      if nodes[a]['matrix'][i][h] is not None
                                      and nodes[b]['matrix'][h][j] is not None]
                        row.append(max(candidates) if candidates else None)
                    expected.append(row)
                wa, wb = words[a], words[b]
                if wa[0] and wb[0] and wa[2] == wb[1]: return False
                word = (wa[0] + wb[0], wa[1] if wa[0] else wb[1], wb[2] if wb[0] else wa[2])
            else: return False
            if matrix != expected: return False
            words.append(word)
        out = cert['output_node']
        if type(out) is not int or not 0 <= out < len(nodes): return False
        word = words[out]
        if word[0] != length - 1 or (word[0] and word[1] != 'A'): return False
        expected_table = []
        for a in (0, 1):
            if a and not eligible[0]: continue
            direction = 1 if (a == 1) == first_is_row else -1
            i = INDEX[a, direction]
            for j, (b, d) in enumerate(STATES):
                z = nodes[out]['matrix'][i][j]
                if z is not None:
                    expected_table.append(dict(first=a, last=b, direction=d, score=a * weight + z))
        expected_table.sort(key=lambda x: (x['first'], x['last'], x['direction']))
        if type(cert['table']) is not list: return False
        for entry in cert['table']:
            if type(entry) is not dict or set(entry) != {'first', 'last', 'direction', 'score'}: return False
            if any(type(value) is not int for value in entry.values()): return False
        return cert['table'] == expected_table
    except (ValueError, TypeError, KeyError, IndexError, AttributeError, OverflowError):
        return False
