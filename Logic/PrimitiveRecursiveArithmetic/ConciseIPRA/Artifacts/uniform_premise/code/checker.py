import json
k = 0
i = lambda a, t=None, d=0: [i(b, t, d + 5 - len(a)) for b in a] if isinstance(a, list) else a if k <= a < d else d % 2 and i(t, d=3)

def c(a, g):
    global k
    if i(a) in g:
        return
    m, s, u, t = q()
    c(m, g)
    if m in ([s, u], not s and [t] * 3) and i(t, u) == a:
        a = i(t, s)
    h = m * 3 or ([[s and [s], u, t], i(t, [s, u, t], 3) if s else u] if u else (a := i(*a, t, 2)))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or len(a) % 2 == u) and k)])
q = json.load(open(0)).pop
c(q(), [[]])
print('ACCEPT')
