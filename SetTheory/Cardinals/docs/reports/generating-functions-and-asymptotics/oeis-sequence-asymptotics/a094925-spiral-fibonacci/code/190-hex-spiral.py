"""Two independent finite realizations of the hexagonal adjacency recurrence."""
from __future__ import annotations

DIRECTIONS = ((-1, -1), (-2, 0), (-1, 1), (1, 1), (2, 0), (1, -1))


def integer(value, name, minimum=0):
    if type(value) is not int:
        raise TypeError(name + ' must be an integer, not bool or float')
    if value < minimum:
        raise ValueError(name + ' is outside its domain')
    return value


def delay_table(stages):
    integer(stages, 'stages')
    rows = [(), (), ()]
    for r in range(1, stages + 1):
        for side in range(6):
            length = r + (side == 4)
            delay = 6 * r - 4 + side
            for position in range(length):
                n = len(rows)
                rows.append((n - delay - 1,) if position == length - 1
                            else (n - delay - 1, n - delay))
    return rows


def validate_rows(rows):
    if type(rows) is not list or len(rows) < 3:
        raise TypeError('rows must be a list containing the initial three rows')
    for n, row in enumerate(rows):
        if type(row) is not tuple:
            raise TypeError('each extra-neighbor row must be a tuple')
        if n < 3:
            if row:
                raise ValueError('the initial extra-neighbor rows must be empty')
        elif not 1 <= len(row) <= 2:
            raise ValueError('invalid extra-neighbor degree')
        if any(type(j) is not int for j in row):
            raise TypeError('neighbor indices must be integers, not booleans')
        if any(j < 0 or j >= n - 2 for j in row):
            raise ValueError('extra neighbors must precede both recurrence predecessors')
        if tuple(sorted(set(row))) != row:
            raise ValueError('neighbor indices must be distinct and increasing')
    return rows


def values(rows, a0=0, a1=1):
    integer(a0, 'a0')
    integer(a1, 'a1', 1)
    validate_rows(rows)
    sequence = [a0, a1]
    for n in range(2, len(rows)):
        sequence.append(sequence[n - 1] + sequence[n - 2]
                        + sum(sequence[j] for j in rows[n]))
    return sequence


def coordinate_model(stages, a0=0, a1=1):
    """Walk lattice edges, discover occupied neighbors, and sum their values.

    This routine never consults delay_table or values. One vertex beyond the
    final recurrence row is generated so the same complete stages are covered.
    """
    integer(stages, 'stages')
    integer(a0, 'a0')
    integer(a1, 'a1', 1)
    final_n = 3 * stages * stages + 4 * stages + 2
    vertices = [(0, 0), (2, 0)]
    for r in range(1, stages + 2):
        for side, (dx, dy) in enumerate(DIRECTIONS):
            for _ in range(r + (side == 4)):
                x, y = vertices[-1]
                vertices.append((x + dx, y + dy))
                if len(vertices) > final_n:
                    break
            if len(vertices) > final_n:
                break
        if len(vertices) > final_n:
            break
    seen = {vertices[0]: 0}
    sequence = [a0, a1]
    rows = [(), ()]
    for n in range(2, final_n + 1):
        current = vertices[n - 1]
        if current in seen:
            raise ValueError('coordinate walk revisited a vertex')
        seen[current] = n - 1
        x, y = current
        neighbors = sorted(seen[(x + dx, y + dy)] for dx, dy in DIRECTIONS
                           if (x + dx, y + dy) in seen)
        if n - 2 not in neighbors:
            raise ValueError('path predecessor is not adjacent')
        sequence.append(sequence[-1] + sum(sequence[j] for j in neighbors))
        rows.append(tuple(j for j in neighbors if j != n - 2))
    return sequence, rows
