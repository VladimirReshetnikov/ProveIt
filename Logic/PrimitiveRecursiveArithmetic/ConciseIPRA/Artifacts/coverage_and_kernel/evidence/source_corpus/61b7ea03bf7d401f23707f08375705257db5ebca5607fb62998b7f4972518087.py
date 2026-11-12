import json
k = 0
i = lambda a, t=0j, d=0: [i(b, t, d + b' \x02\x01\x04'[len(a)]) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g):
    global k
    if i(a) in g:
        return
    m, s, u, t = q()
    if m:
        c(m, g)
        a = m in ([s, u], not s and [t]) and i(t, u) == a and i(t, s) or a
        h = m[2:]
    elif t:
        h = a = i(a[2], t, 2)
    else:
        n, t, r = s
        h = [[u and [n], t, r], i(r, s, 1) if u else t]
    k -= 1
    c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])
try:
    c((q := json.load(open(0)).pop)(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
