"""Deliberately dense mathematical oracle, separate from all production code."""

def dense_replay(real, n, passive, schedule, *, zero_fill_only=False):
    a = [[row.get(h, 0) for h in range(n)] for row in real]
    b = [[row.get(h, 0) for h in range(n)] for row in passive]
    live, active = set(range(n)), set(range(len(a)))
    for r, g in schedule:
        if r not in active or g not in live or a[r][g] != 1:
            raise ValueError('not an actual positive singleton schedule')
        active.remove(r); live.remove(g)
        if zero_fill_only and any(a[j][g] * a[r][h] for j in active for h in live):
            raise ValueError('nonzero fill')
        for row in [a[j] for j in sorted(active)] + b:
            w = row[g]
            for h in live:
                row[h] += w * a[r][h]
            row[g] = 0
    if active:
        raise ValueError('incomplete')
    return b, sorted(live)


def private_rows(b, live, deleted=frozenset()):
    ans = [-1] * len(b)
    for i, row in enumerate(b):
        if i in deleted:
            continue
        for h in live:
            if row[h] == 1 and all(j == i or j in deleted or other[h] == 0
                                   for j, other in enumerate(b)):
                ans[i] = h
                break
    return tuple(ans)


def dense_saturated(real, n, passive, schedule):
    """Matches the maintained dense matrix/private-choice loop, without geometry."""
    a = [[min(2, row.get(h, 0)) for h in range(n)] for row in real]
    b = [[min(2, row.get(h, 0)) for h in range(n)] for row in passive]
    active, live = set(range(len(a))), set(range(n))
    for r, g in schedule:
        if r not in active or g not in live or a[r][g] != 1:
            raise ValueError('invalid')
        active.remove(r); live.remove(g)
        for row in [a[j] for j in sorted(active)] + b:
            w = row[g]
            for h in live:
                row[h] = min(2, row[h] + w * a[r][h])
            row[g] = 0
    if active:
        raise ValueError('incomplete')
    return private_rows(b, sorted(live))
