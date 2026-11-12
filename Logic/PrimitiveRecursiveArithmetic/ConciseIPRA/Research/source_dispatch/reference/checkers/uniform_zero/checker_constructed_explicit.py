import json

def c(a, g=[], k=0):
    i = lambda a, t=0j, d=0: [i(b, t, d + 5 - len(a)) for b in a] if isinstance(a, list) else a or 1 if k <= a < d else d % 2 and i(t, d=3)
    if i(a) in g:
        return
    m, s, u, t = q()
    if m:
        c((m := ([s, u] if s else t and [t] * 3 or m)), g, k)
        a = i(t, u) == a and i(t, s) or a
    h = m * 3 or (u and [[s and [s], u, t], i(t, [s, u, t], 3) if s else u]) or (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) % 2 == m) and k)], k)
q = json.load(open(0)).pop
c(q())
print('ACCEPT')

