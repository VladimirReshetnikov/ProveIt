#!/usr/bin/env python3
"""Independent finite exact checks. Python standard library only; no assertions.
This program is evidence for finite identities, never a substitute for the
analytic argument or the arithmetic G-function theorem cited in the report.
"""
from collections import defaultdict
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parent
FILES = frozenset({"README.md", "verify.py", "negative_tests.py", "evidence.json",
    "provenance.json", "b279571.txt", "historical_gmp_n0_1000.txt",
    "enumerate_gmp.cpp", "historical_verification.json", "manifest.sha256"})
PUBLIC_HASH = "9fa7ab4c890fd441996ad028a2bd25c9ef69904c13f1a383371023627ac37c65"

class CheckError(Exception):
    pass

def require(condition, message):
    if not condition:
        raise CheckError(message)

def same(actual, expected, message):
    require(actual == expected, message)

def unique_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, "JSON: duplicate key " + key)
        out[key] = value
    return out

def load_json(name):
    try:
        return json.loads((ROOT / name).read_text(encoding="utf-8"),
                          object_pairs_hook=unique_object,
                          parse_constant=lambda s: (_ for _ in ()).throw(CheckError("JSON: nonfinite number")))
    except (ValueError, UnicodeError) as exc:
        raise CheckError("JSON: invalid " + name) from exc

def keys(value, expected, path):
    require(type(value) is dict and set(value) == set(expected), "SCHEMA: " + path + " keys")

def integer(value, path, minimum=None):
    require(type(value) is int and (minimum is None or value >= minimum), "SCHEMA: " + path + " integer")
    return value

def rational(value, path):
    require(type(value) is str and re.fullmatch(r"-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?", value) is not None,
            "SCHEMA: " + path + " canonical rational")
    q = Q(value)
    require(str(q) == value, "SCHEMA: " + path + " canonical rational")
    return q

def vector(value, size, path):
    require(type(value) is list and len(value) == size, "SCHEMA: " + path + " shape")
    return [rational(v, path + "[" + str(i) + "]") for i, v in enumerate(value)]

def matrix(value, path):
    require(type(value) is list and len(value) == 2, "SCHEMA: " + path + " shape")
    return [vector(row, 2, path + "[" + str(i) + "]") for i, row in enumerate(value)]

def state(value, path):
    require(type(value) is list and len(value) == 3, "SCHEMA: " + path + " state")
    integer(value[0], path + ".a", 0); integer(value[1], path + ".b", 0)
    require(value[2] in ("P", "Q"), "SCHEMA: " + path + " color")
    return tuple(value)

def steps(value, path):
    require(type(value) is list and len(value) > 0, "SCHEMA: " + path + " steps")
    for i, pair in enumerate(value):
        require(type(pair) is list and len(pair) == 2 and pair[0] in ("PP", "QP", "PQ", "QQ"),
                "SCHEMA: " + path + " edge")
        integer(pair[1], path + " parameter", 0 if pair[0] == "PP" else 1)
    return value

def inventory():
    actual = {p.name for p in ROOT.iterdir()}
    same(actual, FILES, "INVENTORY: unexpected or missing member")
    require(all((ROOT / n).is_file() and not (ROOT / n).is_symlink() for n in FILES),
            "INVENTORY: members must be regular nonsymlink files")
    entries = {}
    for line in (ROOT / "manifest.sha256").read_text(encoding="ascii").splitlines():
        require(re.fullmatch(r"[0-9a-f]{64}  [A-Za-z0-9_.-]+", line) is not None,
                "MANIFEST: malformed entry")
        digest, name = line.split("  ")
        require(name not in entries, "MANIFEST: duplicate member")
        entries[name] = digest
    same(set(entries), FILES - {"manifest.sha256"}, "MANIFEST: closed inventory mismatch")
    for name in sorted(entries):
        same(sha256((ROOT / name).read_bytes()).hexdigest(), entries[name], "HASH: " + name)

def evidence():
    d = load_json("evidence.json")
    ks = {"schema", "ranges", "critical", "right_vector", "stationary", "color_matrix", "drift",
          "corrector", "covariance", "determinant", "correlation_squared", "reverse_drift",
          "reverse_corrector", "double_angle_cosine", "twice_double_angle_cosine",
          "inverse_coefficients", "dual_seed", "dual_repeat", "loops", "initial_measure"}
    keys(d, ks, "evidence")
    same(d["schema"], "a279571-finite-exact-v1", "SCHEMA: evidence version")
    keys(d["ranges"], {"brute", "tree", "endpoint", "reversal", "external"}, "ranges")
    for k, v in d["ranges"].items(): integer(v, "ranges." + k, 0)
    same(d["ranges"], {"brute":9, "tree":65, "endpoint":12, "reversal":5, "external":1000},
         "RANGE: mandatory coverage changed")
    d["critical"] = vector(d["critical"], 3, "critical")
    for k in ("right_vector", "stationary", "inverse_coefficients", "initial_measure"):
        d[k] = vector(d[k], 2, k)
    for k in ("color_matrix", "drift", "corrector", "covariance", "reverse_drift", "reverse_corrector"):
        d[k] = matrix(d[k], k)
    for k in ("determinant", "correlation_squared", "double_angle_cosine", "twice_double_angle_cosine"):
        d[k] = rational(d[k], k)
    keys(d["dual_seed"], {"start", "steps", "end"}, "dual_seed")
    for k in ("start", "end"): d["dual_seed"][k] = state(d["dual_seed"][k], "dual_seed."+k)
    steps(d["dual_seed"]["steps"], "dual_seed")
    steps(d["dual_repeat"], "dual_repeat")
    require(type(d["loops"]) is list and len(d["loops"]) == 6, "SCHEMA: loops shape")
    for i, loop in enumerate(d["loops"]):
        keys(loop, {"start", "steps"}, "loop")
        loop["start"] = state(loop["start"], "loop.start")
        steps(loop["steps"], "loop")
    return d

# A sparse multivariate rational polynomial engine, written here rather than
# importing the earlier SymPy verifier. Variable order is x,y,z,lambda.
ZERO = (0, 0, 0, 0)
def clean(p): return {m:Q(c) for m,c in p.items() if c}
def const(c): return {ZERO:Q(c)} if c else {}
def var(i):
    m = list(ZERO); m[i] = 1
    return {tuple(m):Q(1)}
def add(*ps):
    out = defaultdict(Q)
    for p in ps:
        for m,c in p.items(): out[m] += c
    return clean(out)
def scale(p, c): return clean({m:v*c for m,v in p.items()})
def sub(p,q): return add(p,scale(q,-1))
def mul(*ps):
    out = const(1)
    for p in ps:
        nxt = defaultdict(Q)
        for m,a in out.items():
            for n,b in p.items(): nxt[tuple(u+v for u,v in zip(m,n))] += a*b
        out = clean(nxt)
    return out
def derivative(p,i):
    out = {}
    for m,c in p.items():
        if m[i]:
            n = list(m); n[i] -= 1; out[tuple(n)] = c*m[i]
    return out
def evaluate(p, values):
    out = Q(0)
    for m,c in p.items():
        for i,power in enumerate(m): c *= values[i]**power
        out += c
    return out

def algebra(d):
    x,y,z,l = [var(i) for i in range(4)]; one = const(1)
    xy = sub(x,y); ym = sub(y,one); oy = sub(one,y); xm = sub(x,one)
    # Derive the cleared determinant of lambda*I-M, not an assumed root.
    a = sub(mul(l,xy),mul(x,x)); b = sub(mul(l,ym),x)
    D = sub(mul(a,b),mul(x,x))
    Dclaimed = add(mul(l,l,xy,ym),scale(mul(l,add(mul(x,x,ym),mul(x,xy))),-1),mul(x,x,xm))
    same(D,Dclaimed,"ALGEBRA: characteristic determinant")
    # Derive K from the 2x2 cleared functional system.
    K = add(mul(sub(xy,mul(z,x,x)),add(oy,mul(z,x))),mul(z,z,x,x))
    Kclaimed = add(mul(xy,oy),scale(mul(z,x,x,oy),-1),mul(z,x,xy),scale(mul(z,z,x,x,xm),-1))
    same(K,Kclaimed,"ALGEBRA: kernel determinant")
    # Check the polynomial coefficients and discriminant without root sampling.
    B = sub(sub(sub(mul(z,x,x),mul(z,x)),x),one)
    C = sub(x,mul(z,z,x,x,xm))
    same(K,add(mul(y,y),mul(B,y),C),"ALGEBRA: quadratic kernel")
    disc = sub(mul(B,B),scale(C,4))
    fact = mul(xm,sub(mul(z,x),one),add(mul(z,x,x),scale(mul(z,x),3),scale(x,-1),one))
    same(disc,fact,"ALGEBRA: discriminant factorization")
    disc9 = defaultdict(Q)
    for mon,c in disc.items():
        mm = list(mon); mm[2] = 0; disc9[tuple(mm)] += c*Q(1,9)**mon[2]
    same(clean(disc9),scale(mul(sub(x,one),sub(x,const(3)),sub(x,const(3)),sub(x,const(9))),Q(1,81)),
         "ALGEBRA: critical discriminant")
    xc,yc,lc = d["critical"]; at = [xc,yc,Q(1,9),lc]
    require(xc > yc > 1 and lc > 0,"TILT: convergence region")
    same(evaluate(D,at),0,"TILT: characteristic root")
    same([evaluate(derivative(D,i),at) for i in (0,1)],[0,0],"TILT: stationary critical point")
    same(evaluate(K,at),0,"ALGEBRA: critical kernel root")
    same(evaluate(derivative(K,1),at),0,"ALGEBRA: critical double y root")
    dl = evaluate(derivative(D,3),at)
    require(dl != 0,"TILT: simple Perron root")
    hessian = [[-at[i]*at[j]*evaluate(derivative(derivative(D,i),j),at)/(lc*dl) for j in (0,1)] for i in (0,1)]
    same(hessian,d["covariance"],"COVARIANCE: Perron Hessian mismatch")
    M = [[xc*xc/(xc-yc),xc/(yc-1)],[xc/(xc-yc),xc/(yc-1)]]
    r = d["right_vector"]
    require(all(t>0 for t in r),"TILT: positive Perron vector")
    same([sum(M[i][j]*r[j] for j in range(2)) for i in range(2)],[lc*v for v in r],"TILT: right eigenvector")
    same(M[0][0]+M[1][1]-lc,Q(9,4),"TILT: second eigenvalue")
    same([[M[i][j]*r[j]/(lc*r[i]) for j in range(2)] for i in range(2)],d["color_matrix"],"TILT: color matrix")
    # Kernel transport is elimination of a linear equation, with no assertion
    # of a globally contracting orbit. Multipliers are checked polynomially.
    A_num = sub(xy,mul(z,x,xm))
    rhs_H = mul(z,x,A_num)
    same(rhs_H,sub(mul(z,x,xy),mul(z,z,x,x,xm)),"ALGEBRA: affine transport coefficient")
    return K

# Each family: old color, new color, first parameter, alpha, ratio, base, slope.
FAMILIES = {
 "PP": (0,0,0,Q(1,3),Q(5,9),(1,0),(-1,1)),
 "QP": (1,0,1,Q(2,5),Q(5,9),(1,-1),(-1,1)),
 "PQ": (0,1,1,Q(1,6),Q(3,5),(1,0),(0,-1)),
 "QQ": (1,1,1,Q(1,3),Q(3,5),(1,0),(0,-1))}
COLORS = ("P","Q")

def family_moments(k0,alpha,r):
    s0 = r**k0/(1-r)
    s1 = r**k0*(k0/(1-r)+r/(1-r)**2)
    s2 = r**k0*(k0*k0/(1-r)+2*k0*r/(1-r)**2+r*(1+r)/(1-r)**3)
    return [alpha*s0,alpha*s1,alpha*s2]

def moments(reverse, pi):
    P = [[Q(0) for j in range(2)] for i in range(2)]
    E = [[[Q(0) for a in range(2)] for j in range(2)] for i in range(2)]
    V = [[[[Q(0) for b in range(2)] for a in range(2)] for j in range(2)] for i in range(2)]
    for i,j,k0,alpha,r,base,slope in FAMILIES.values():
        if reverse:
            alpha *= pi[i]/pi[j]; i,j = j,i
            base = tuple(-v for v in base); slope = tuple(-v for v in slope)
        s0,s1,s2 = family_moments(k0,alpha,r)
        P[i][j] += s0
        for a in range(2):
            E[i][j][a] += base[a]*s0+slope[a]*s1
            for b in range(2):
                V[i][j][a][b] += base[a]*base[b]*s0+(base[a]*slope[b]+slope[a]*base[b])*s1+slope[a]*slope[b]*s2
    return P,E,V

def stochastic(d):
    pi=d["stationary"]; r=d["right_vector"]; xc,yc,lc=d["critical"]
    same(sum(pi),1,"CHAIN: stationary normalization")
    require(all(v>0 for v in pi),"CHAIN: stationary positivity")
    # Check geometric families against individual telescoping tilt formulas.
    for family,(i,j,k0,alpha,rho,base,slope) in FAMILIES.items():
        require(0<rho<1,"CHAIN: geometric tail")
        for k in (k0,k0+1,k0+5):
            a,b=(base[t]+slope[t]*k for t in range(2))
            same(alpha*rho**k,xc**a*yc**b*r[j]/(lc*r[i]),"TILT: individual edge "+family)
    for reverse in (False,True):
        P,E,V = moments(reverse,pi)
        same(P,d["color_matrix"],"CHAIN: reversed color matrix" if reverse else "CHAIN: geometric row sums")
        same([sum(row) for row in P],[1,1],"CHAIN: row normalization")
        same([sum(pi[i]*P[i][j] for i in range(2)) for j in range(2)],pi,"CHAIN: stationarity")
        require(all(v>0 for row in P for v in row),"CHAIN: primitive color chain")
        m=[[sum(E[i][j][a] for j in range(2)) for a in range(2)] for i in range(2)]
        same(m,d["reverse_drift" if reverse else "drift"],"CHAIN: reverse drift" if reverse else "CHAIN: drift")
        h=d["reverse_corrector" if reverse else "corrector"]
        same([sum(pi[i]*m[i][a] for i in range(2)) for a in range(2)],[0,0],"CHAIN: zero stationary drift")
        same([sum(pi[i]*h[i][a] for i in range(2)) for a in range(2)],[0,0],"CORRECTOR: mean zero")
        same([[h[i][a]-sum(P[i][j]*h[j][a] for j in range(2)) for a in range(2)] for i in range(2)],m,"CORRECTOR: Poisson equation")
        cov=[[Q(0),Q(0)],[Q(0),Q(0)]]
        for a in range(2):
            for b in range(2):
                for i in range(2):
                    for j in range(2):
                        da=h[j][a]-h[i][a]; db=h[j][b]-h[i][b]
                        cov[a][b] += pi[i]*(V[i][j][a][b]+da*E[i][j][b]+db*E[i][j][a]+da*db*P[i][j])
        same(cov,d["covariance"],"COVARIANCE: reverse martingale mismatch" if reverse else "COVARIANCE: martingale mismatch")
    s=d["covariance"]; det=s[0][0]*s[1][1]-s[0][1]*s[1][0]
    same(det,d["determinant"],"COVARIANCE: determinant")
    require(s[0][0]>0 and det>0 and s[0][1]<0 and s[0][1]==s[1][0],"COVARIANCE: positive definite signed matrix")
    c2=s[0][1]**2/(s[0][0]*s[1][1]); same(c2,d["correlation_squared"],"ANGLE: squared cosine")
    same(2*c2-1,d["double_angle_cosine"],"ARITHMETIC: double angle")
    v=2*d["double_angle_cosine"]; same(v,d["twice_double_angle_cosine"],"ARITHMETIC: twice double angle")
    require(v.denominator != 1,"ARITHMETIC: rational noninteger premise")
    # cos(pi/4)^2 < cos(theta)^2 < cos(pi/5)^2=(3+sqrt(5))/8.
    require(Q(1,2)<c2 and 8*c2-3>0 and (8*c2-3)**2<5,"ARITHMETIC: 4<p<5 comparison")
    # Formal coefficients of log y and kappa*loglog y after inversion.
    u,v=d["inverse_coefficients"]
    same([u-1,v-1],[0,0],"INVERSE: logarithmic coefficient cancellation")

def displacement(fam,k):
    i,j,k0,alpha,r,base,slope=FAMILIES[fam]
    require(type(k) is int and k>=k0,"EDGE: parameter out of range")
    return i,j,tuple(base[t]+slope[t]*k for t in range(2)),alpha*r**k

def in_D(s): return s[0]>=0 and s[1]>=0 and ((s[2]=="P" and s[0]+s[1]>=1) or (s[2]=="Q" and s[0]>=1))

def walk(start,seq,pi,reverse=False,domain=True):
    cur=start; prob=Q(1)
    for fam,k in seq:
        i,j,v,q=displacement(fam,k)
        if reverse:
            q *= pi[i]/pi[j]; i,j=j,i; v=tuple(-t for t in v)
        require(cur[2]==COLORS[i],"EDGE: color mismatch")
        cur=(cur[0]+v[0],cur[1]+v[1],COLORS[j])
        require(cur[0]>=0 and cur[1]>=0,"EDGE: path leaves quadrant")
        if domain: require(in_D(cur),"EDGE: path leaves reachable domain")
        prob *= q
    return cur,prob

def paths(d):
    pi=d["stationary"]
    expected_starts=[(1,0,"P"),(1,0,"P"),(0,1,"P"),(0,1,"P"),(1,0,"Q"),(1,0,"Q")]
    for i,loop in enumerate(d["loops"]):
        same(loop["start"],expected_starts[i],"LOOP: boundary coverage")
        same(len(loop["steps"]),3+i%2,"LOOP: length coverage")
        end,p=walk(loop["start"],loop["steps"],pi)
        same(end,loop["start"],"LOOP: return mismatch")
        same(p,Q(1,9)**len(loop["steps"]),"LOOP: telescoping probability")
        # Reversal checks every listed edge and the entire loop probability.
        rev=list(reversed(loop["steps"]))
        same(walk(end,rev,pi,True),(loop["start"],p),"LOOP: reverse mismatch")
        for da,db in ((1,0),(0,1),(4,7)):
            st=(loop["start"][0]+da,loop["start"][1]+db,loop["start"][2])
            same(walk(st,loop["steps"],pi),(st,p),"LOOP: translated template")
    seed=d["dual_seed"]; same(seed["start"],(1,0,"P"),"DUAL: seed start")
    end,p=walk(seed["start"],seed["steps"],pi,True)
    same(end,seed["end"],"DUAL: seed endpoint"); same(end,(1,3,"P"),"DUAL: seed interior")
    require(p>0,"DUAL: seed probability")
    new,p=walk(end,d["dual_repeat"],pi,True)
    same(new,(end[0]+1,end[1]+1,"P"),"DUAL: repeat displacement")
    require(p>0,"DUAL: repeat probability")
    # Forward arbitrary-depth seed uses PP parameters 0 and 1.
    same(walk((0,0,"P"),[["PP",0],["PP",1]],pi,domain=False)[0],(1,1,"P"),"SEED: forward diagonal")
    same(d["initial_measure"],[Q(1,3),Q(5,27)],"RESOLVENT: first-step measure")
    for (a,b,c),want in zip(((1,0,"P"),(0,1,"P")),d["initial_measure"]):
        same(displacement("PP",b)[3],want,"RESOLVENT: first-step tilt")

# Two genuinely different enumerators: original avoidance and label transitions.
def avoids_extension(e,x):
    return not any(e[i]>e[j] and e[j]<=x and e[i]>=x for i in range(len(e)) for j in range(i+1,len(e)))

def brute_levels(N):
    seqs=[()]; levels=[{(0,0,"P"):1}]
    for n in range(1,N+1):
        seqs=[e+(x,) for e in seqs for x in range(n) if avoids_extension(e,x)]
        counts=defaultdict(int)
        for e in seqs:
            h=max(e); c="P" if e[-1]==h else "Q"
            b=sum(avoids_extension(e,x) for x in range(e[-1] if c=="Q" else h))
            counts[(n-h,b,c)] += 1
            require(avoids_extension(e,n),"MONOTONICITY: append-maximum injection")
        levels.append(dict(counts))
    return levels

def tree_levels(N):
    D={(0,0,"P"):1}; levels=[D]
    for n in range(N):
        E=defaultdict(int)
        for (a,b,c),v in D.items():
            for k in range(0 if c=="P" else 1,a+1): E[(a+1-k,b+k-(c=="Q"),"P")]+=v
            for j in range(1,b+1): E[(a+1,b-j,"Q")]+=v
        D=dict(E); levels.append(D)
    return levels

def prefix_levels(N):
    # Solve for predecessor labels, using diagonal prefixes and row suffixes.
    P={(0,0):1}; T={}; levels=[{(0,0,"P"):1}]
    for n in range(N):
        U={}; V={}
        for total in range(1,n+2):
            sp=sq=0
            for b in range(total):
                sp+=P.get((total-1-b,b),0); sq+=T.get((total-b,b),0)
                if sp+sq: U[(total-b,b)]=sp+sq
        for A in range(1,n+2):
            tail=0
            for b in range(n+1-A,-1,-1):
                if tail: V[(A,b)]=tail
                tail+=P.get((A-1,b),0)+T.get((A-1,b),0)
        P,T=U,V
        levels.append({**{(a,b,"P"):v for (a,b),v in P.items()},**{(a,b,"Q"):v for (a,b),v in T.items()}})
    return levels

def typ(level,c): return {(a,b,0,0):Q(v) for (a,b,t),v in level.items() if t==c}

def functional(levels,K):
    x,y,z,l=[var(i) for i in range(4)]; one=const(1); xy=sub(x,y); oy=sub(one,y)
    slices=[]
    for k in range(3):
        slices.append({(m[0],m[1],0,m[3]):v for m,v in K.items() if m[2]==k})
    Fs=[];Hs=[];Js=[]
    for lev in levels:
        p=typ(lev,"P");q=typ(lev,"Q");f=add(p,q)
        h=defaultdict(Q);j=defaultdict(Q)
        for (a,b,t),v in lev.items():
            h[(a,0,0,0)]+=v; j[(0,a+b+(t=="P"),0,0)]+=v
        Fs.append(f);Hs.append(clean(h));Js.append(clean(j))
    for n in range(len(levels)):
        p=typ(levels[n],"P");q=typ(levels[n],"Q")
        if n==0:
            same(p,const(1),"FUNCTIONAL: root P");same(q,{},"FUNCTIONAL: root Q")
        else:
            pp=typ(levels[n-1],"P");qq=typ(levels[n-1],"Q")
            same(mul(xy,p),sub(add(mul(x,x,pp),mul(x,qq)),mul(x,Js[n-1])),"FUNCTIONAL: P equation n="+str(n))
            same(mul(oy,q),mul(x,sub(Hs[n-1],Fs[n-1])),"FUNCTIONAL: Q equation n="+str(n))
        lhs=add(*(mul(slices[k],Fs[n-k]) for k in range(min(2,n)+1)))
        rhs=mul(oy,xy) if n==0 else sub(mul(x,xy,Hs[n-1]),mul(x,oy,Js[n-1]))
        if n>=2: rhs=sub(rhs,mul(x,x,sub(x,one),Hs[n-2]))
        same(lhs,rhs,"FUNCTIONAL: eliminated equation n="+str(n))

def killed_level(D,pi,reverse=False):
    E=defaultdict(Q)
    for (a,b,c),v in D.items():
        for fam,(i,j,k0,alpha,r,base,slope) in FAMILIES.items():
            if reverse:
                if c!=COLORS[j]: continue
                # Reverse PP/QP: y decreases with k; reverse PQ/QQ: x--
                # and y may grow without bound. For finite detailed-balance
                # checks use a bounded terminal box, not an infinite sum.
                raise CheckError("INTERNAL: unbounded reverse enumerator not used")
            if c!=COLORS[i]: continue
            kmax=a+1 if fam in ("PP","QP") else b
            for k in range(k0,kmax+1):
                ii,jj,w,q=displacement(fam,k)
                na,nb=a+w[0],b+w[1]
                if na>=0 and nb>=0: E[(na,nb,COLORS[jj])]+=v*q
    return dict(E)

def endpoint(d,levels):
    pi=d["stationary"];r=d["right_vector"];N=d["ranges"]["endpoint"]
    D={(0,0,"P"):Q(1)}
    for m in range(N):
        expected={(a-1,b,c):v for (a,b,c),v in levels[m+1].items()}
        same(set(D),set(expected),"ENDPOINT: support n="+str(m+1))
        for (a,b,c),v in D.items():
            count=2*9**m*Q(1,3)**a*Q(3,5)**b/r[COLORS.index(c)]*v
            same(count,expected[(a,b,c)],"ENDPOINT: tilted count n="+str(m+1))
        weighted=sum(Q(1,3)**a*Q(3,5)**b/r[COLORS.index(c)]*v for (a,b,c),v in D.items())
        same(2*9**m*weighted,sum(levels[m+1].values()),"ENDPOINT: count total")
        if m>=1:
            require(all(in_D(st) for st in D),"DOMAIN: reachable state outside D")
        D=killed_level(D,pi)
    # Independent reverse-edge detailed balance on all finite successful paths
    # in a fixed box. Both kernels use the same box, so they are finite matrices.
    box=[(a,b,c) for a in range(4) for b in range(4) for c in COLORS]
    edges={}; dual={}
    for s in box:
        for fam,(i,j,k0,alpha,rho,base,slope) in FAMILIES.items():
            if s[2]!=COLORS[i]: continue
            for k in range(k0,8):
                ii,jj,v,q=displacement(fam,k);t=(s[0]+v[0],s[1]+v[1],COLORS[jj])
                if t in box:
                    edges[s,t]=edges.get((s,t),Q(0))+q
                    dual[t,s]=dual.get((t,s),Q(0))+pi[i]/pi[j]*q
    K={(s,s):Q(1) for s in box};R=K.copy()
    for n in range(1,d["ranges"]["reversal"]+1):
        def compose(A,B):
            out=defaultdict(Q)
            by=defaultdict(list)
            for (u,t),q in B.items(): by[u].append((t,q))
            for (s,u),p in A.items():
                for t,q in by[u]: out[s,t]+=p*q
            return dict(out)
        K=compose(K,edges);R=compose(R,dual)
        same(set(K),{(t,s) for s,t in R},"REVERSAL: support")
        for (s,t),v in K.items():
            same(pi[COLORS.index(s[2])]*v,pi[COLORS.index(t[2])]*R[t,s],"REVERSAL: killed path balance")
    # Scalar resolvent coefficients use first-step v and 18*z^2.
    D={(1,0,"P"):d["initial_measure"][0],(0,1,"P"):d["initial_measure"][1]}
    for n in range(2,N+1):
        g=sum(Q(1,3)**a*Q(3,5)**b/r[COLORS.index(c)]*v for (a,b,c),v in D.items())
        same(18*9**(n-2)*g,sum(levels[n].values()),"RESOLVENT: coefficient n="+str(n))
        D=killed_level(D,pi)

def read_table(name):
    raw=(ROOT/name).read_bytes()
    try: lines=raw.decode("ascii").splitlines()
    except UnicodeError as exc: raise CheckError("TABLE: non-ASCII "+name) from exc
    out=[]
    for i,line in enumerate(lines):
        require(re.fullmatch(r"(?:0|[1-9][0-9]*) (?:0|[1-9][0-9]*)",line) is not None,"TABLE: noncanonical row "+name)
        a,b=map(int,line.split());same(a,i,"TABLE: consecutive indices "+name);out.append(b)
    same(len(out),1001,"TABLE: required 1001 rows "+name)
    return raw,out

def provenance():
    d=load_json("provenance.json")
    keys(d,{"schema","public_table","historical_recomputation","analytic_report","fresh_retrieval","analytic_scope"},"provenance")
    same(d["schema"],"a279571-provenance-v1","SCHEMA: provenance version")
    p=d["public_table"]
    keys(p,{"file","url","download_url","attribution","sha256","rows","archived_retrieval_date"},"public_table")
    same(p["file"],"b279571.txt","PROVENANCE: public filename")
    same(p["url"],"https://oeis.org/A279571/b279571.txt","PROVENANCE: public URL")
    same(p["download_url"],p["url"]+"?download=1","PROVENANCE: retrieval URL")
    same(p["sha256"],PUBLIC_HASH,"PROVENANCE: public hash anchor")
    same(p["rows"],1001,"PROVENANCE: public range"); require(type(p["rows"]) is int,"SCHEMA: rows integer")
    same(p["archived_retrieval_date"],"2026-10-02","PROVENANCE: source date")
    same(p["attribution"],"Nicholas R. Beaton; terms 0..32 from Vaclav Kotesovec","PROVENANCE: source attribution")
    same(d["historical_recomputation"],{"file":"historical_gmp_n0_1000.txt","role":"internally generated, not an external source","status":"archived exact GMP run; all 1001 rows compared here; not rerun by default"},"PROVENANCE: historical role")
    same(d["analytic_report"],{"file":"../report123.tex","role":"analytic arguments supplied in the accompanying report, whose bytes are sealed by the outer inventory; not proved by this checker"},"PROVENANCE: proof boundary")
    require(type(d["fresh_retrieval"]) is dict and type(d["fresh_retrieval"].get("entry_checked")) is bool and type(d["fresh_retrieval"].get("raw_bytes_refetched")) is bool,"SCHEMA: retrieval booleans")
    same(d["fresh_retrieval"],{"date":"2026-10-02","entry_url":"https://oeis.org/A279571","entry_checked":True,"raw_bytes_refetched":False,"limitation":"OEIS entry and attribution independently verified; fresh raw b-file retrieval failed with web cache miss and HTTP 403"},"PROVENANCE: fresh retrieval boundary")
    same(d["analytic_scope"],"Finite exact checks do not prove the FCLT, LLT, annulus transfer, bridge estimates, logarithmic asymptotic theorem, critical-circle continuation, G-function theorem, or non-D-finiteness.","PROVENANCE: finite-check scope")
    h=load_json("historical_verification.json")
    keys(h,{"algorithm","arithmetic","verified_terms","all_match_published_bfile","data_sha256","compile","run"},"historical_verification")
    same(h["algorithm"],"independent diagonal-prefix and row-suffix exact DP","HISTORICAL: algorithm")
    same(h["arithmetic"],"GMP integers","HISTORICAL: arithmetic")
    same(h["verified_terms"],1001,"HISTORICAL: term count");require(type(h["verified_terms"]) is int,"SCHEMA: historical count integer")
    same(h["all_match_published_bfile"],True,"HISTORICAL: recorded match"); require(type(h["all_match_published_bfile"]) is bool,"SCHEMA: historical boolean")
    same(h["data_sha256"],PUBLIC_HASH,"HISTORICAL: table hash")
    same(h["compile"],"g++ -O3 -std=c++17 enumerate.cpp -lgmpxx -lgmp -o enumerate","HISTORICAL: original compile command")
    same(h["run"],"./enumerate 1000","HISTORICAL: original run command")
    a,A=read_table("b279571.txt");b,B=read_table("historical_gmp_n0_1000.txt")
    same(sha256(a).hexdigest(),PUBLIC_HASH,"TABLE: public source hash")
    same(sha256(b).hexdigest(),PUBLIC_HASH,"TABLE: historical output hash")
    same(A,B,"TABLE: historical 1001 coefficient comparison")
    return A

def main():
    require(len(sys.argv)==1 or (len(sys.argv)==3 and sys.argv[1]=="--output"),"USAGE: python3 verify.py [--output PATH]")
    output=Path(sys.argv[2]).resolve() if len(sys.argv)==3 else None
    if output is not None:
        require(ROOT != output and ROOT not in output.parents,"OUTPUT: path must be outside sealed checks directory")
    inventory(); d=evidence(); public=provenance()
    K=algebra(d);stochastic(d);paths(d)
    levels=tree_levels(d["ranges"]["tree"])
    same(levels,prefix_levels(d["ranges"]["tree"]),"ENUMERATION: tree/prefix full-state mismatch")
    same(levels[:10],brute_levels(d["ranges"]["brute"]),"ENUMERATION: original avoidance/full-state mismatch")
    same([sum(v.values()) for v in levels],public[:len(levels)],"ENUMERATION: published coefficient mismatch")
    for n,level in enumerate(levels[1:],1):
        require(all(a>=1 and b>=0 and a+b<=n and (c!="Q" or a>=2) for a,b,c in level),"DOMAIN: unshifted labels or automatic sum bound")
    functional(levels,K);endpoint(d,levels)
    inventory()
    print("PASS: strict schema, canonical rationals, closed inventory, SHA-256 anchors")
    print("PASS: original avoidance/full states n=0..9; tree/prefix full states and external coefficients n=0..65")
    print("PASS: cleared functional equations and eliminated kernel equation n=0..65; exact determinant/discriminants")
    print("PASS: Perron tilt, stationary chain, two forward covariance derivations, reverse martingale covariance")
    print("PASS: six boundary return-loop templates, reversed edges, dual seed and repeat, initial resolvent measure")
    print("PASS: endpoint count/resolvent identities n=1..12; finite-box path reversal lengths 1..5")
    print("PASS: irrationality premises, exact 4<p<5 comparison, inverse logarithmic coefficient algebra")
    print("PASS: archived public/historical GMP table equality for all 1001 coefficients; fresh GMP run not required")
    print("LIMIT: finite checks do not prove the analytic or arithmetic external theorems; see README.md")
    if output is not None:
        result={"schema":"a279571-finite-exact-results-v1","status":"PASS","ranges":d["ranges"],"exact_arithmetic":"Python standard-library fractions.Fraction and arbitrary-precision integers","public_table_sha256":PUBLIC_HASH,"historical_gmp_comparison_rows":1001,"fresh_gmp_run":False,"analytic_proof_certified_by_finite_checks":False,"source_unchanged":True}
        output.parent.mkdir(parents=True,exist_ok=True)
        output.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    return 0

if __name__=="__main__":
    try:
        sys.exit(main())
    except CheckError as exc:
        print("FAIL: "+str(exc),file=sys.stderr)
        sys.exit(1)
    except (OSError,UnicodeError) as exc:
        print("FAIL: IO: "+str(exc),file=sys.stderr)
        sys.exit(1)
