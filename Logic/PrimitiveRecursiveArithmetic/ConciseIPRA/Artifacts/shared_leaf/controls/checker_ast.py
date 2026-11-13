from json import loads

def c(k, a, *g):
    def i(a, t=None, d=0):
        try:
            return [i(b, t, d + 5 - len(a)) for b in a]
        except:
            return a if k <= a < d else d % 2 and i(t, d=3)
    while i(a) not in g:
        s, u, t = r = loads(input())
        if a == [[s and [s], u, t], i(t, r, 3) if s else u]:
            return
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        g += (i(c(k, s, *g) or s * 3 or (a := i(*a, t, 2)), (k := k - 1) * (1 if s else len(a) == 2)),)
        a = i(a, [k])
c(0, loads(input()), 0)
print('ACCEPT')
