"""Independent replay of forest contraction and geometric singleton cancellations.

The source-parallelity checker authenticates the handle charts.  This checker
reconstructs all counts from those charts, accepts no count summaries, and
imports no producer code or group-presentation simplifier.
"""

from .integer_codec import certificate_equal
from .column_cancellation_verify import verify_column_cancellations


def verify_core_handlebody_certificate(core, certificate, *, check=lambda: None):
    """Check a core certificate, conditional on authenticated geometric charts."""
    check()
    required = {'schema', 'method', 'forest', 'cancellations', 'components'}
    if type(certificate) is not dict or set(certificate) != required:
        return False
    version, method = certificate['schema'], certificate['method']
    supported = ((version == 'normal-core-handlebody-v1' and method in ('leaf', 'capped'))
                 or (version == 'normal-core-handlebody-v2' and method == 'column_leaf'))
    if not supported or core['handles3']:
        return False
    forest, moves = certificate['forest'], certificate['cancellations']
    if type(forest) is not list or type(moves) is not list:
        return False
    vertices, edges, discs = [core[f'handles{i}'] for i in range(3)]
    for handles in (vertices, edges, discs):
        if any(type(h['id']) is not int or h['id'] != i for i, h in enumerate(handles)):
            return False
    if not vertices:
        return False
    n, m = len(vertices), len(edges)
    sets = [{i} for i in range(n)]
    owner = list(range(n))
    seen = set()
    for e in forest:
        check()
        if type(e) is not int or e < 0 or e >= m or e in seen:
            return False
        seen.add(e)
        a, b = edges[e]['ends']
        if type(a) is not int or type(b) is not int or not (0 <= a < n and 0 <= b < n):
            return False
        x, y = owner[a], owner[b]
        if x == y:
            return False
        low, high = min(x, y), max(x, y)
        for point in sets[high]:
            owner[point] = low
        sets[low].update(sets[high])
        sets[high].clear()
    for edge in edges:
        check()
        a, b = edge['ends']
        if type(a) is not int or type(b) is not int or not (0 <= a < n and 0 <= b < n):
            return False
        if owner[a] != owner[b]:
            return False  # The supplied forest must span every 0/1 component.

    # Reconstruct the raw intersection matrix, including repeated occurrences.
    matrix = []
    for disc in discs:
        check()
        cycle = disc['cycle']
        if type(cycle) is not list or not cycle or len(cycle) % 2:
            return False
        row = {}
        for j in range(0, len(cycle), 2):
            point, crossing = cycle[j], cycle[j + 1]
            if point['dimension'] != 0 or crossing['dimension'] != 1:
                return False
            v, e = point['handle'], crossing['handle']
            following = cycle[(j + 2) % len(cycle)]['handle']
            if any(type(x) is not int for x in (v, e, following)):
                return False
            if not (0 <= v < n and 0 <= following < n and 0 <= e < m):
                return False
            if sorted((v, following)) != sorted(edges[e]['ends']):
                return False
            if e not in seen:
                row[e] = min(2, row.get(e, 0) + 1)
        matrix.append(row)
    live_rows = set(range(len(discs)))
    live_columns = set(range(m)) - seen
    if method == 'column_leaf':
        if not verify_column_cancellations(dict(enumerate(matrix)), moves, check=check):
            return False
        for r, c in moves:
            check()
            if c not in live_columns:
                return False
            live_rows.remove(r)
            live_columns.remove(c)
        moves = []
    elif method == 'leaf':
        # Independently check a triangular source pattern.  Earlier leaf
        # removals add no other crossings, so timestamps replace all updates.
        removed_at = {}
        for time, move in enumerate(moves):
            check()
            if type(move) is not list or len(move) != 2:
                return False
            r, c = move
            if type(r) is not int or type(c) is not int:
                return False
            if r not in live_rows or c not in live_columns:
                return False
            if matrix[r].get(c, 0) != 1:
                return False
            if any(h != c and h not in removed_at for h in matrix[r]):
                return False
            live_rows.remove(r)
            live_columns.remove(c)
            removed_at[c] = time
        moves = []
    else:
        matrix = [[row.get(c, 0) for c in range(m)] for row in matrix]
    for move in moves:
        check()
        if type(move) is not list or len(move) != 2:
            return False
        r, c = move
        if type(r) is not int or type(c) is not int:
            return False
        if r not in live_rows or c not in live_columns or matrix[r][c] != 1:
            return False
        live_rows.remove(r)
        live_columns.remove(c)
        for i in live_rows:
            check()
            for h in live_columns:
                matrix[i][h] = min(2, matrix[i][h] + matrix[i][c] * matrix[r][h])
            matrix[i][c] = 0
    if live_rows:
        return False
    expected = []
    for component in sorted(set(owner)):
        points = [v for v in range(n) if owner[v] == component]
        loops = [e for e in sorted(live_columns) if owner[edges[e]['ends'][0]] == component]
        expected.append(dict(id=component, zero_handles=points,
                             remaining_one_handles=loops, genus=len(loops)))
    check()
    return certificate_equal(certificate['components'], expected)
