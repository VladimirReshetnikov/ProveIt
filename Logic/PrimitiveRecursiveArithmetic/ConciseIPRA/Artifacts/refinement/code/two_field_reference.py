import json

def c(a, g=[0], k=0):
    i = lambda a, t=c, d=0: [i(b, t, d + 5 - len(a)) for b in a] if a * 0 != 0 else a if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    try:
        b, r = a
        n, b, h = b
        if n:
            n, = n
            b = i(h, [n, b, h], 3)
        if b == r:
            return
    except:
        pass
    m, t = q()
    c(m, g, k)
    if m and 1 < len(m) < 4:
        s, u = m if len(m) == 2 else (0, t)
        t = t if len(m) == 2 else m[-1]
        if i(t, u) != a:
            raise ValueError
        a = i(t, s)
    h = m * 3 or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) == 2) and k)], k)
q = json.load(open(0)).pop
c(q())
print('ACCEPT')
