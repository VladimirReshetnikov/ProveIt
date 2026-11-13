import json

def c(a, g, k=0):
    i = lambda a, t=None, d=0: [i(b, t, d + b' \x02\x01\x04'[len(a)]) for b in a] if a * 0 == [] else a if k <= a < d else d % 2 and i(t, d=1)
    if i(a) in g:
        return
    m, s, u, t = q()
    if m:
        c(m, g, k)
        if m in ([s, u], not s and [t]) and i(t, u) == a:
            a = i(t, s)
        h = m[2:]
    elif t:
        h = a = i(a[2], t, 2)
    else:
        n, t, u = s
        h = [s, i(u, i([*n, t, u], d=1), 1) if n else t]
    k -= 1
    c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)], k)
try:
    q = json.load(open(0)).pop
    c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
