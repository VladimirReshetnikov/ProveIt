import json
k = 0


def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \2\1\4'[len(a)]) for b in a + []]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)


def c(a, g):
    global k
    if not i(a):
        return 1
    m, t = q()
    try:
        p, b = g[m]
        return i(b, t) == a and c(p, g)
    except:
        if m and c(m, g):
            k -= 1
            if m[2:]:
                b = i(m[2:], k)[0]
                h = [i(b, 0), b]
            else:
                s, u = m
                h = [i(t, s), i(t, u)]
            return c(a, g + [h])
        elif t:
            a = i(a[2], t, 2)
            k -= 1
            return c(i(a, [k]), g + [[0, i(a, 0)], [0, len(a) % 2 or i(a, k)]])
        else:
            (n, t, r), b = a
            if n:
                n, = n
                t = i(r, [n, t, r], 1)
            return b == t


try:
    q = json.load(open(0)).pop
    1 / c(q(), [])
except:
    print('REJECT')
    raise SystemExit(1)
print('ACCEPT')
