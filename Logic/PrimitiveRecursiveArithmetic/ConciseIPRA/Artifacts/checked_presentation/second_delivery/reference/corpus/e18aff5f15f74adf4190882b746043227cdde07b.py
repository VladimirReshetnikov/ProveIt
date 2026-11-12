from json import load

def c(a, g=(0,), k=0):

    def i(a, t=None, d=0):
        try:
            return [i(b, t, d + 5 - len(a)) for b in a]
        except:
            return a if k <= a < d else d % 2 and i(t, d=3)
    while i(a) not in g:
        m, s, u, t = q()
        if m == ([s, u] if s else [t] * 3) and i(t, u) == a:
            a = i(t, s)
        h = c(m, g, k) or m * 3 or ([[s and [s], u, t], i(t, [s, u, t], 3) if s else u] if u else (a := i(*a, t, 2)))
        k -= 1
        g += (i(h, (m or len(a) == 2) and k),)
        a = i(a, [k])
c((q := load(open(0)).pop)())
print('ACCEPT')

