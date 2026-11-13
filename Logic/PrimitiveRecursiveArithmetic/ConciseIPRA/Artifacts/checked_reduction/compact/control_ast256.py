from json import loads

def i(a, t=0j, d=(k := 0)):
    try:
        return [i(b, t, d + 5 - len(a)) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=3)

def c(g, a):
    match loads(input()):
        case [s, u, t] as r:
            global k
    if i(a) not in (*g, [[s and [s], u, t], i(t, r, 3) if s else u]):
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        c([*g, i(s * 3 or (a := i(*a, t, 2)), (c(g, s) or s or len(a) == 2) and k)], i(a, [k]))
    k -= 1
c(b'\x00', loads(input()))
print('ACCEPT')
