from json import load
k = 0

def i(a, t=0j, d=0):
    try:
        return [i(b, t, d + 5 - len(a)) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=3)

def c(a, g):
    global k
    while i(a) not in g:
        m, *r = q()
        s, u, t = r
        if i(t, u) == a:
            m = r[:2] if s else [t] * 3
            a = i(t, s)
        h = c(m, g) or m * 3 if m else [[s and [s], u, t], i(t, r, 3) if s else u] if u else (a := i(*a, t, 2))
        k -= 1
        g += (i(h, (m or len(a) == 2) and k),)
        a = i(a, [k])

def v(a, n=0):
    if a * 0 == 0:
        return n and (a == 0 or (a > 2 and a % 2))
    r = len(a)
    return r in ([1, 3] if n else [1, 2]) and all((v(x, n or r == 2) for x in a)) and (n or r == 2 or len(a[0]) == 1 or all((b[:2] == [5, 0] for b in a[0])))
p = load(open(0))
if set(str(p)) - set(' [],-0123456789'):
    raise ValueError
q = p.pop
a = q()
if not v(a):
    raise ValueError
c(a, ())
print('ACCEPT')
