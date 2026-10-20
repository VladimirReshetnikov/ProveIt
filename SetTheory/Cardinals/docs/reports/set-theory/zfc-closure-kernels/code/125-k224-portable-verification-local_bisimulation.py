"""Finite certificates for all-register equivalence of closed source blocks.

A relation connects decrement instructions and normal returns. Between related
instructions, the accumulated vector of increments must agree exactly. Every
pair of related decrements tests and changes the same register, and their two
successors are related. Induction on these segments gives both directions for
all natural register vectors, including divergence. The search fuel here is
only the size of a finite source graph; it is not an execution-time bound.
"""

def leaf(node):
    return isinstance(node[0], str)


def sites(node, prefix=''):
    if leaf(node):
        return [[prefix, *node]]
    return sites(node[0], prefix + '0') + sites(node[1], prefix + '1')


def graph(node):
    rows = sites(node)
    intervals = {}

    def visit(part, prefix, start):
        if leaf(part):
            end = start + 1
        else:
            middle = visit(part[0], prefix + '0', start)
            end = visit(part[1], prefix + '1', middle)
        intervals[prefix] = start, end
        return end

    visit(node, '', 0)

    def unwind(prefix, edge, depth):
        while prefix:
            last, prefix = prefix[-1], prefix[:-1]
            if last == edge:
                depth -= 1
                if not depth:
                    return intervals[prefix][1 if edge == '0' else 0]
        raise ValueError('Control escapes the claimed closed local block')

    result = []
    for index, (prefix, operation, argument) in enumerate(rows):
        if operation == 'CI':
            row = 'INC', argument, index + 1
        elif operation == 'CD':
            row = 'DEC', argument, unwind(prefix, '0', 1), index + 1
        elif operation == 'CB':
            row = 'GOTO', unwind(prefix, '0', argument)
        elif operation == 'CC':
            row = 'GOTO', unwind(prefix, '1', argument)
        elif operation == 'CH':
            row = 'HALT',
        else:
            raise ValueError('Unknown source instruction')
        result.append(row)
    result.append(('RETURN',))
    return result


def segment(graph_rows, position):
    increments = [0] * 9
    visited = set()
    while True:
        if position in visited:
            raise ValueError('An infinite test-free source segment needs a separate certificate')
        visited.add(position)
        row = graph_rows[position]
        if row[0] in ('DEC', 'RETURN', 'HALT'):
            return position, tuple(increments)
        if row[0] == 'INC':
            increments[row[1]] += 1
            position = row[2]
        else:
            assert row[0] == 'GOTO'
            position = row[1]


def check(old, new):
    left, right = graph(old), graph(new)
    pending = [(0, 0)]
    seen = set()
    certificate = []
    while pending:
        old_entry, new_entry = pending.pop()
        i, increments_i = segment(left, old_entry)
        j, increments_j = segment(right, new_entry)
        if increments_i != increments_j:
            raise ValueError(('Increment vectors differ', old_entry, new_entry,
                              increments_i, increments_j))
        if (i, j) in seen:
            continue
        seen.add((i, j))
        a, b = left[i], right[j]
        if a[0] != b[0]:
            raise ValueError(('Different boundary operations', i, j, a, b))
        if a[0] == 'DEC':
            if a[1] != b[1]:
                raise ValueError(('Different tested registers', i, j, a, b))
            pending.extend(zip(a[2:], b[2:]))
        certificate.append({'old': i, 'new': j, 'opcode': a[0],
                            'register': a[1] if a[0] == 'DEC' else None})
    return {'status': 'ALL_REGISTER_LOCAL_BISIMULATION_PASS',
            'old_leaves': len(left) - 1, 'new_leaves': len(right) - 1,
            'test_pairs': len(certificate), 'pairs': certificate}
