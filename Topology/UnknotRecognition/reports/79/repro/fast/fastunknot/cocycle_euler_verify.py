"""Independent weak-duality check for a weighted difference optimization.

This arithmetic certificate proves no manifold or knot property. The caller
supplies the indexed objective and difference constraints being certified.
"""
from .integer_codec import encoded_integer


def verify_difference_optimum(n, edges, constraints, certificate, *, check=lambda: None):
    """Certify min sum w*abs(c+p[b]-p[a]), subject to p[b]-p[a] <= d.

    A balanced signed edge flow in [-w,w] and nonnegative constraint flow
    give a lower bound sum(f*c)-sum(lambda*d). Equality proves optimality
    over real potentials as well as integer ones. No solver is imported.
    """
    check()
    fields = {'schema', 'potential', 'edge_flows', 'constraint_flows', 'objective'}
    if (type(n) is not int or n < 1 or type(edges) is not list
            or type(constraints) is not list or type(certificate) is not dict
            or set(certificate) != fields
            or certificate['schema'] != 'weighted-difference-optimum-v1'):
        return False
    for key, size in [('potential', n), ('edge_flows', len(edges)),
                      ('constraint_flows', len(constraints))]:
        if type(certificate[key]) is not list or len(certificate[key]) != size:
            return False
    try:
        potential = [encoded_integer(x) for x in certificate['potential']]
        objective = encoded_integer(certificate['objective'])
    except ValueError:
        return False
    balance, primal, dual = [0]*n, 0, 0
    for row, supplied in zip(edges, certificate['edge_flows']):
        check()
        if type(row) is not list or len(row) != 4:
            return False
        a, b, offset, weight = row
        if any(type(v) is not int or not 0 <= v < n for v in (a, b)):
            return False
        try:
            c, w, f = map(encoded_integer, (offset, weight, supplied))
        except ValueError:
            return False
        if w < 0 or not -w <= f <= w:
            return False
        primal += w*abs(c+potential[b]-potential[a])
        dual += f*c
        balance[a] -= f
        balance[b] += f
    for row, supplied in zip(constraints, certificate['constraint_flows']):
        check()
        if type(row) is not list or len(row) != 3:
            return False
        a, b, bound = row
        if any(type(v) is not int or not 0 <= v < n for v in (a, b)):
            return False
        try:
            d, flow = map(encoded_integer, (bound, supplied))
        except ValueError:
            return False
        if flow < 0 or potential[b]-potential[a] > d:
            return False
        dual -= flow*d
        balance[a] -= flow
        balance[b] += flow
    check()
    return not any(balance) and primal == dual == objective
