"""Independent fixed-seed coefficient check; Python standard library only."""
def add(a, b):
    c = [0] * max(len(a), len(b))
    for i, v in enumerate(a):
        c[i] += v
    for i, v in enumerate(b):
        c[i] += v
    while len(c) > 1 and c[-1] == 0:
        c.pop()
    return c

def shift(a, k):
    return [0] * k + a

P = [[1], [1]]
for n in range(1, 160):
    next_p = add(add(P[n], shift(P[n], 1)), shift(P[n], 2))
    next_p = add(next_p, [-v for v in shift(P[n-1], 1)])
    P.append(next_p)

assert P[4] == [1, 0, 3, 2, 4, 2, 1]
assert all(p[3]**2 < p[2]*p[4] for p in P[3:])
assert all(p[2] > p[3] < p[4] for p in P[4:])
print("PASS: exact fixed-seed checks through n=160")
