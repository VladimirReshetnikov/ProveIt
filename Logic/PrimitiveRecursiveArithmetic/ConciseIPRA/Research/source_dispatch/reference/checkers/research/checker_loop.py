from json import load
k = 0
def i(a, t=None, d=0):
    try:
        return [i(b, t, d + b' \x02\x01\x04'[len(a)]) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)

def c(a, g):
    global k
    while i(a) not in g:
        m, s, u, t = q()
        if m:
            c(m, g)
            if m in ([s, u], not s and [t]) and i(t, u) == a:
                a = i(t, s)
            h = m[2:]
        elif m is None:
            h = [[s, u, t], i(t, [list(*s), u, t], 1) if s else u]
        else:
            h = a = i(a[2], t, 2)
        k -= 1
        g += i(h, k if m or len(a) % 2 == m else 0),
        a = i(a, [k])
try:
    q = load(open(0)).pop
    c(q(), ())
except:
    print('REJECT')
    raise
print('ACCEPT')

