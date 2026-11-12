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
        m, s, u, t = q()
        if i(t, u) == a:
            m = [s, u] if s else [t] * 3
            a = i(t, s)
        h = c(m, g) or m * 3 if m else [[s and [s], u, t], i(t, [s, u, t], 3) if s else u] if u else (a := i(*a, t, 2))
        k -= 1
        g += (i(h, (m or len(a) == 2) and k),)
        a = i(a, [k])
q = load(open(0)).pop
c(q(), ())
print('ACCEPT')
