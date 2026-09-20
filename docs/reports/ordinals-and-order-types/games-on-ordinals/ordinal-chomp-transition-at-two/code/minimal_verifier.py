# Self-contained proof certificate for S=<4,5,6>. Python 3.10+.
# Value 3 is the symbol "at least 3", not an exact nimber.
from functools import lru_cache

gaps = (1, 2, 3, 7)
shapes = tuple(range(8)) + (15,)

def member(n):
    return n >= 0 and n not in gaps

def elements(c):
    return {g for i, g in enumerate(gaps) if c >> i & 1}

def encode(values):
    return sum(1 << i for i, g in enumerate(gaps) if g in values)

def low_mex(options):
    return next((i for i in range(3) if i not in options), 3)

@lru_cache(None)
def value(position):
    return low_mex({value(tuple(z for z in position
                                if not member(z-y)))
                    for y in position})

def position(x, c):
    return (tuple(n for n in range(x) if member(n))
            + tuple(x+g for g in sorted(elements(c))))

def delta(d, c):
    return encode({g for g in gaps if g < d or g-d in elements(c)})

def cut(a, c):
    return encode({g for g in elements(c) if not member(g-a)})

rows = {x: {c: value(position(x, c)) for c in shapes}
        for x in range(8, 15)}
far = {0}
for b in (4, 5, 6):
    apery = tuple(n for n in range(b+8)
                  if member(n) and not member(n-b))
    assert value(apery) == 3
states = {}
for x in range(15, 52):
    states[x] = (tuple(sorted(far)),
                 tuple(tuple(rows[t][c] for c in shapes)
                       for t in range(x-7, x)))
    if x == 51:
        break
    row = {}
    for c in sorted(shapes, key=int.bit_count):
        near = {rows[x-d][delta(d, c)] for d in range(1, 8)}
        tail = {row[cut(a, c)] for a in elements(c)}
        row[c] = low_mex(far | near | tail)
    rows[x] = row
    if rows[x-7][15] < 3:
        far.add(rows[x-7][15])
assert all(rows[x][15] == 3 for x in rows)
assert states[43] == states[51]
print("PASS: 387 entries; state 43 = state 51; period 8.")
