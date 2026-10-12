"""Independent replay of source geometric dual 2/3 cancellation forests.

Source and geometry authentication belongs to normal_parallelity_verify.
This checker reconstructs cap occurrences and imports no forest producer.
It does not infer cap incidence from signed algebraic boundary coefficients.
"""

from .integer_codec import encoded_integer


def replay_source_core_dual(geometry, certificate, *, check=lambda: None):
    """Return the reduced chart on success and None for a malformed proof."""
    check()
    if (type(certificate) is not dict or set(certificate) != {'schema', 'forest'}
            or certificate['schema'] != 'source-core-dual-forest-v1'
            or type(certificate['forest']) is not list):
        return None
    selected = []
    for value in certificate['forest']:
        try:
            selected.append(encoded_integer(value))
        except ValueError:
            return None
    core, coordinates = geometry['core'], geometry['coordinates']
    three, two = core['handles3'], core['handles2']
    n, m = len(three), len(two)
    if len(selected) != n:
        return None
    if any(e < 0 or e >= m for e in selected):
        return None
    locations = [n] * (4 * len(coordinates))
    for i, handle in enumerate(three):
        check()
        if type(handle['id']) is not int or handle['id'] != i:
            return None
        for t, corner in handle['link_triangles']:
            check()
            if (type(t) is not int or type(corner) is not int or
                    not 0 <= t < len(coordinates) or not 0 <= corner < 4 or
                    locations[4*t + corner] != n):
                return None
            locations[4*t + corner] = i
    for i, handle in enumerate(two):
        check()
        if type(handle['id']) is not int or handle['id'] != i:
            return None

    parent = list(range(n + 1))
    sizes = [1] * (n + 1)

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    # n is the exposed-boundary root in this independent replay.  Source edge
    # roots are local representatives of parity zero, so their smaller local
    # endpoint is rank zero even when the global edge is a loop.
    representatives = ((0, 1, 0), (0, 2, 1), (0, 3, 2),
                       (1, 2, 2), (1, 3, 1), (2, 3, 0))
    for e in selected:
        check()
        h = two[e]
        if (type(h['edge']) is not int or
                not 0 <= h['edge'] < 6 * len(coordinates) or
                type(h['rank']) is not int or h['rank'] < 0):
            return None
        t, position = divmod(h['edge'], 6)
        a, b, q = representatives[position]
        row = coordinates[t]
        w = row[a] + row[b] + row[4] + row[5] + row[6] - row[4 + q]
        left, right = locations[4*t + a], locations[4*t + b]
        if w == 0:
            if h['rank'] != 0:
                return None
        elif h['rank'] == 0:
            right = n
        elif h['rank'] == w:
            left = n
        else:
            return None
        a, b = find(left), find(right)
        if a == b:
            return None
        if sizes[a] < sizes[b]:
            a, b = b, a
        parent[b] = a
        sizes[a] += sizes[b]
    if any(find(v) != find(n) for v in range(n)):
        return None
    removed = [False] * m
    for e in selected:
        removed[e] = True
    remaining = [dict(h, id=j) for j, h in enumerate(
        handle for handle in two if not removed[handle['id']])]
    check()
    return dict(geometry, core=dict(core, handles2=remaining, handles3=[]))
