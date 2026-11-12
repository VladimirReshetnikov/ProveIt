from json import loads

def c(k, a, *g):

    def i(a, t=None, d=0):
        try:
            return [i(b, t, d + 5 - len(a)) for b in a]
        except:
            return a if k <= a < d else d % 2 and i(t, d=3)
    while i(a) not in g:
        s, u, t = r = q()
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
            u = 0
        g += (i([[s and [s], u, t], i(t, r, 3) if s else u] if u else c(k, s, *g) or s * 3 or (a := i(*a, t, 2)), (k := (k - 1)) and (s or len(a) == 2) and k),)
        a = i(a, [k])
c(0, (q := loads(input()).pop)(), 0)
print('ACCEPT')
