import json
k = 0

def i(a, t=0j, d=0):
    try:
        return [i(b, t, d + 5 - len(a)) for b in a]
    except:
        return a if k <= a < d else d % 2 and i(t, d=3)

def c(g, a):
    global k
    s, u, t = r = q()
    if i(a) not in (*g, [[s and [s], u, t], i(t, r, 3) if s else u]):
        if i(t, u) == a:
            a = i(t, s)
            s = r[:2] if s else [t] * 3
        c([*g, i(s * 3 or (a := i(*a, t, 2)), c(g, s) or k * bool(s or len(a) == 2))], i(a, [k]))
    k -= 1
q = json.load(open(0)).pop
c(b'\x00', q())
print('ACCEPT')
