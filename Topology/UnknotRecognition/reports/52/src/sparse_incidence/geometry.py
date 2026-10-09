"""Input contract and nonexpanding marked-union construction.

Pairings use inclusive endpoints [a,b,c,d,sign], sign +/-1.
Ports use half-open intervals [lo,hi). Empty intervals are discarded.
"""

def natural(value, name='value'):
    if type(value) is not int or value < 0:
        raise ValueError(name + ' must be a nonnegative integer, not bool')
    return value

def union_intervals(intervals):
    result = []
    for lo, hi in sorted(intervals):
        if lo == hi:
            continue
        if result and lo <= result[-1][1]:
            result[-1] = (result[-1][0], max(hi, result[-1][1]))
        else:
            result.append((lo, hi))
    return tuple(result)

def prepare(size, pairings, ports, check=lambda: None):
    natural(size, 'size')
    rows = []
    for row in pairings:
        check()
        if not isinstance(row, (list, tuple)) or len(row) != 5:
            raise ValueError('pairing row must have five entries')
        a, b, c, d, sign = row
        for v in (a, b, c, d):
            natural(v, 'pairing endpoint')
        if type(sign) is not int or sign not in (-1, 1):
            raise ValueError('pairing sign must be +/-1')
        if not (a <= b < size and c <= d < size and b-a == d-c):
            raise ValueError('invalid pairing interval or unequal widths')
        if c < a:
            a, b, c, d = c, d, a, b
        rows.append((a, b, c, d, sign))
    clean = []
    for port in ports:
        check()
        intervals = []
        for interval in port:
            check()
            if not isinstance(interval, (list, tuple)) or len(interval) != 2:
                raise ValueError('a port interval must have two endpoints')
            lo, hi = interval
            natural(lo, 'port endpoint'); natural(hi, 'port endpoint')
            if not lo <= hi <= size:
                raise ValueError('port interval outside universe or reversed')
            intervals.append((lo, hi))
        clean.append(union_intervals(intervals))
    return size, tuple(rows), tuple(clean)

def selected_union(ports, mask, check=lambda: None):
    natural(mask, 'mask')
    if mask >= 1 << len(ports):
        raise ValueError('mask outside port set')
    intervals = []
    while mask:
        check()
        bit = mask & -mask
        intervals.extend(ports[bit.bit_length()-1])
        mask ^= bit
    return union_intervals(intervals)

def cone_rows(union):
    if not union:
        return ()
    result = []
    anchor = union[0][0]
    for lo, hi in union:
        if hi-lo >= 2:
            result.append((lo, hi-2, lo+1, hi-1, 1))
        if lo != anchor:
            result.append((anchor, anchor, lo, lo, 1))
    return tuple(result)
