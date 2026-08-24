from fractions import Fraction
def qp(u,p): return ((pow(u,p-1,p*p)-1)//p) % p

# ---- p=101 via exact class counting (equivalent to brute force, no floats) ----
def classcheck(p):
    p2=p*p
    units=[u for u in range(1,p2) if u%p!=0]
    q={u:qp(u,p) for u in units}
    from collections import Counter
    cnt=Counter(q.values())
    assert set(cnt)==set(range(p)), "q_p not surjective"
    assert set(cnt.values())=={p-1}, f"fibers not uniform: {set(cnt.values())}"
    q2,q3=q[2],q[3]
    # zero set size
    zpairs=[(x,y) for x in range(p) for y in range(p) if (x*q3-y*q2)%p==0]
    Zsize=len(zpairs)*(p-1)**2
    # control-twist classes: {(t*q2, t*q3) : t in 0..p-1}
    cpairs=set(((t*q2)%p,(t*q3)%p) for t in range(p))
    Csize=len(cpairs)*(p-1)**2
    tot=(p*(p-1))**2
    eq = set(zpairs)==cpairs
    print(f"p={p}: q2={q2} q3={q3} |Z|={Zsize} |C|={Csize} EQUAL={eq} |Z|/tot={Fraction(Zsize,tot)} |Z|/p^4={Fraction(Zsize,p**4)} vs (p-1)^2/p^3={Fraction((p-1)**2,p**3)}")
    return eq

for p in [5,7,11,13,17,19,23,29,31,101,1093,3511]:
    classcheck(p)
