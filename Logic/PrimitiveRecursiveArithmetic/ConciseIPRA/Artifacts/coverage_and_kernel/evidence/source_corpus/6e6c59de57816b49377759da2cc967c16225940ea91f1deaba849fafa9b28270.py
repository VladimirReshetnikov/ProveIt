from json import *
k = 0

def i(a, t=0j, d=0):
    try:
        return [i(b, t, d + b' BAD'[len(a)] % 8) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=1)

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
        n, t, u = s
        h = [[n and [n], t, u], i(u, s, 1) if n else t]
    k -= 1
    c(i(a, [k]), g + [i(h, k if m or len(a) % 2 == m else 0)])
c((q := load(open(0)).pop)(), [])
print('ACCEPT')
