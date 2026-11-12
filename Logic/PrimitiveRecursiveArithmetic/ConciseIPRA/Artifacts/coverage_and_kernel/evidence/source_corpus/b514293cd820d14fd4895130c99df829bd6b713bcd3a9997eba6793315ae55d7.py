from json import load
def i(a, t=None, d=(k := 0)):
    try:
        return [i(b,t,d+b' \2\1\4'[len(a)]) for b in a+[]]
    except:
        return a if k <= a < d else d % 2 and i(t,d=1)

def c(a, g):
    global k
    if i(a) in g:
        return
    m, s, u, t = q()
    if m:
        c(m, g)
        a = a if (h := m[2:]) else m in ([s, u], not s and [t]) and i(t, u) == a and i(t, s)
    elif t:
        h = a = i(a[2], t, 2)
    else:
        (n, t, r), b = a
        if n:
            n, = n
            t = i(r, [n, t, r], 1)
        if b == t:
            return
    k -= 1
    c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])

try:
    q = load(open(0)).pop
    c(q(), [])
except:
    print('REJECT')
    raise
print('ACCEPT')
