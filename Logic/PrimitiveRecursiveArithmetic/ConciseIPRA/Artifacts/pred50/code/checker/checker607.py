from json import loads
k = 0

def i(a, t=0j, d=0):
    try:
        return [i(b, t, d + 5 - len(a)) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=3)

def c(a, *g):
    global k
    while i(a) not in g:
        s, u, t = r = loads(input())
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
            u = 0
        h = [[s and [s], u, t], i(t, r, 3) if s else u] if u else s and c(s, *g) or s * 3 or (a := i(*a, t, 2))
        k -= 1
        g += (i(h, (s or len(a) == 2) and k),)
        a = i(a, [k])
c(loads(input()))
print('ACCEPT')
