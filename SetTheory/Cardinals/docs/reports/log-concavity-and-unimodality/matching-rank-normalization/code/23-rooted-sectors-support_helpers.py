"""Boolean Hall tests and the cubic discriminant."""
def hall(core,selected_core,k_left,rs):
    rows=[core[i] for i in selected_core]+[7]*k_left
    cols=[sum(1<<i for i,r in enumerate(rows) if r>>b&1) for b in range(3)]
    cols += [sum(1<<j for j,i in enumerate(selected_core) if r>>i&1) for r in rs]
    for S in range(1,1<<len(cols)):
        union=0
        for j,c in enumerate(cols):
            if S>>j&1:union|=c
        if union.bit_count()<S.bit_count():return False
    return True

def discriminant(c):
    a,b,d,e=c
    return b*b*d*d-4*a*d**3-4*b**3*e-27*a*a*e*e+18*a*b*d*e

