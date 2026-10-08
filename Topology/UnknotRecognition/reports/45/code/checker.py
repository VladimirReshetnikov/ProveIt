"""Independent certificate replay, with no imports from the query producer.

Only algebraic primitive-power claims are checked here. Hashes are not used as
mathematical equality tests. Invalid certificates return False; resource and
cancellation exceptions propagate to the caller as inconclusive.
"""
from math import gcd


def verify_power(rules, cert, *, max_nodes=200_000, max_bits=100_000,
                 check=lambda: None):
    if len(rules) > max_nodes:
        raise RuntimeError('checker node limit')
    if not rules or rules[0] is not None:
        return False
    try:
        root, u, v, d, width = (cert.root, cert.u, cert.v, cert.exponent, cert.width)
    except AttributeError:
        return False
    if any(type(x) is not int for x in (root, u, v, d, width)):
        return False
    if not 0 <= root < len(rules) or d < 1 or gcd(abs(u), abs(v)) != 1:
        return False
    if max(abs(u).bit_length(), abs(v).bit_length(), d.bit_length(), width.bit_length()) > max_bits:
        raise RuntimeError('checker certificate bit limit')
    if width != abs(u)+abs(v)-1:
        return False
    # lengths, signed occurrence counts, endpoints, reduced flag, extremal sums
    lengths = [0]
    counts = [[0]*4]
    endpoints = [(0, 0)]
    good = [True]
    low, high, totals = [0], [0], [0]
    signed = (1, -1, 2, -2)
    for index in range(1, len(rules)):
        check()
        r = rules[index]
        if not isinstance(r, (tuple, list)):
            return False
        if len(r) == 2 and r[0] == 't':
            x = r[1]
            if type(x) is not int or x not in signed:
                return False
            c = [0]*4
            c[signed.index(x)] = 1
            first, last, reduced, n = x, x, True, 1
            h = v if x == 1 else -v if x == -1 else -u if x == 2 else u
            mn, mx, total = min(0, h), max(0, h), h
        elif len(r) == 3 and r[0] == 'c':
            i, j = r[1:]
            if not all(type(t) is int and 0 <= t < index for t in (i, j)):
                return False
            c = [counts[i][k]+counts[j][k] for k in range(4)]
            first = endpoints[i][0] or endpoints[j][0]
            last = endpoints[j][1] or endpoints[i][1]
            reduced = good[i] and good[j] and (not lengths[i] or not lengths[j]
                       or endpoints[i][1] != -endpoints[j][0])
            n = lengths[i]+lengths[j]
            shift = totals[i]
            total = totals[i]+totals[j]
            mn, mx = min(low[i], shift+low[j]), max(high[i], shift+high[j])
        else:
            return False
        if n.bit_length() > max_bits:
            raise RuntimeError('checker bit limit')
        lengths.append(n); counts.append(c); endpoints.append((first, last))
        good.append(reduced); low.append(mn); high.append(mx); totals.append(total)
    check()
    a, A, b, B = counts[root]
    f, l = endpoints[root]
    return (lengths[root] > 0 and good[root] and f != -l
            and not (a and A or b and B) and a-A == d*u and b-B == d*v
            and high[root]-low[root] == width)
