from json import load
k = 0

def i(a, t=0j, d=0):
    try:
        return [i(b, t, d + 5 - len(a)) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=3)

def c(a, g):
    global k
    if i(a) in g:
        return
    m, s, u, t = q()
    if m in ([s, u], 1j if s else [t] * 3) and i(t, u) == a:
        a = i(t, s)
    h = c(m, g) or m * 3 if m else [[s and [s], u, t], i(t, [s, u, t], 3) if s else u] if u else (a := i(*a, t, 2))
    k -= 1
    c(i(a, [k]), g + [i(h, (m or not len(a) % 2) and k)])
q = load(open(0)).pop
c(q(), [])
print('ACCEPT')
