import json
k = 0
i = lambda a, t=None, d=1: [i(b, t, d + (len(a) - 2) % 3) for b in a] if a * 0 == [] else a if k <= a < d else [i(t), 0]

def c(a, g):
    global k
    if i(a) in g:
        return
    m, s, u, t = q()
    if m:
        c(m, g)
        if m in ([s, u], not s and [t] * 3) and i(t, u) == a:
            a = i(t, s)
        h = m * 3
    elif m is None:
        h = [[s and [s] * 4, u, t], i(t, [s, u, t]) if s else u]
    else:
        h = a = i(*a, t, 2)
    k -= 1
    c(i(a, [k] * 4), g + [i(h, (m or len(a) % 2 == m) and k)])
q = json.load(open(0)).pop
c(q(), [])
print('ACCEPT')
