"""Source-checked unit-determinant power-pair elimination in arbitrary groups.

Input rows encode relators x_s^a x_t^{-b}, without expanding exponents. This
local verifier proves the listed pairs trivial from supplied source rows; it
never certifies an arbitrary presentation as a knot input.
"""
def verify_pair(rows,certificate):
    try:
        if not isinstance(certificate,dict) or set(certificate)!={'rows','vertices'}: return False
        ids=certificate['rows'];vs=certificate['vertices']
        if not isinstance(ids,list) or len(ids)!=2 or any(type(i) is not int for i in ids) or ids[0]==ids[1]: return False
        if any(not 0<=i<len(rows) for i in ids): return False
        e,f=rows[ids[0]],rows[ids[1]]
        if any(not isinstance(r,(tuple,list)) or len(r)!=4 or any(type(x) is not int for x in r) for r in (e,f)): return False
        s,t,a,b=e;u,v,c,d=f
        if not 0<s or not 0<t or s==t or (u,v)!=(s,t) or not all((a,b,c,d)): return False
        return type(vs) is list and all(type(x) is int for x in vs) and vs==sorted([s,t]) and abs(a*d-b*c)==1
    except (KeyError,TypeError,IndexError,ValueError): return False

def family(pairs,bits):
    if type(pairs) is not int or type(bits) is not int or pairs<1 or bits<1: raise ValueError()
    M=1<<bits;rows=[];proofs=[]
    for i in range(pairs):
        x=2*i+1;y=x+1;j=len(rows)
        rows.extend([(x,y,M,M+1),(x,y,M+1,M+2)])
        proofs.append({'rows':[j,j+1],'vertices':[x,y]})
    return rows,proofs

def minor_certificate(rows):
    """Produce a short gcd-one minor witness for rows on one ordered pair."""
    from math import gcd
    if not rows: return None
    s,t,_,_=rows[0];g=0;selected=[]
    for i,e in enumerate(rows):
        if len(e)!=4 or tuple(e[:2])!=(s,t) or any(type(z) is not int for z in e) or s<=0 or t<=0 or s==t or not e[2] or not e[3]: raise ValueError('invalid two-power block')
        for j in range(i):
            a,b=e[2:];c,d=rows[j][2:];minor=a*d-b*c
            ng=gcd(g,minor)
            if ng!=g:
                selected.append([i,j]);g=ng
                if g==1:return {'minors':selected,'vertices':sorted([s,t])}
    return None

def verify_minor_certificate(rows,certificate):
    """Independent source-row replay; no call to the producer or verify_pair."""
    from math import gcd
    try:
        if not isinstance(certificate,dict) or set(certificate)!={'minors','vertices'}: return False
        vs=certificate['vertices'];pairs=certificate['minors']
        if not isinstance(vs,list) or len(vs)!=2 or any(type(x) is not int for x in vs) or not 0<vs[0]<vs[1]: return False
        if not isinstance(pairs,list) or not pairs: return False
        g=0;orientation=None
        for pair in pairs:
            if not isinstance(pair,list) or len(pair)!=2 or any(type(j) is not int for j in pair) or pair[0]==pair[1]: return False
            if any(not 0<=j<len(rows) for j in pair): return False
            e,f=rows[pair[0]],rows[pair[1]]
            if any(not isinstance(r,(tuple,list)) or len(r)!=4 or any(type(x) is not int for x in r) for r in (e,f)): return False
            if tuple(e[:2])!=tuple(f[:2]) or sorted(e[:2])!=vs or not all(tuple(e[2:])+tuple(f[2:])): return False
            if orientation is None:orientation=tuple(e[:2])
            if tuple(e[:2])!=orientation:return False
            g=gcd(g,e[2]*f[3]-e[3]*f[2])
        return g==1
    except (KeyError,ValueError,TypeError,IndexError):return False
