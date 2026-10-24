#!/usr/bin/env python3
"""Independent exact audit of emitted packets, using a different ring engine.

No generator or upstream code is imported. JSON expressions are inert ASTs.
This verifies algebraic transformations, not the inherited unbounded theorems.
"""
import ast
from fractions import Fraction
import gzip
import hashlib
import json
from pathlib import Path
import sys

sys.setrecursionlimit(200000)
HERE=Path(__file__).resolve().parent
TOP=(Path(sys.argv[1]).resolve() if len(sys.argv)>1 else HERE.parent)
DIR=TOP/"integer"
P=1000000007
CHECKS=[]

def add(a,b):
    c=dict(a)
    for m,v in b.items():
        c[m]=c.get(m,0)+v
        if not c[m]: del c[m]
    return c

def scale(a,n): return {m:v*n for m,v in a.items() if v*n}

def mul(a,b):
    c={}
    for ma,va in a.items():
        for mb,vb in b.items():
            m=tuple(sorted(ma+mb))
            c[m]=c.get(m,0)+va*vb
    return {m:v for m,v in c.items() if v}

def power(a,k):
    if type(k) is not int or k<0: raise ValueError("invalid power")
    z={():1}
    while k:
        if k&1: z=mul(z,a)
        k//=2
        if k: a=mul(a,a)
    return z

def parse(s, aliases=None):
    aliases=aliases or {}
    def rec(n):
        if isinstance(n,ast.Name): return aliases.get(n.id,{(n.id,):1})
        if isinstance(n,ast.Constant) and type(n.value) is int:
            return {():n.value} if n.value else {}
        if isinstance(n,ast.UnaryOp):
            if isinstance(n.op,ast.USub): return scale(rec(n.operand),-1)
            if isinstance(n.op,ast.UAdd): return rec(n.operand)
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,(ast.Add,ast.Sub)):
                # Flatten large left-associated emitted sums in linear work.
                out={}; stack=[(n,1)]
                while stack:
                    t,sign=stack.pop()
                    if isinstance(t,ast.BinOp) and isinstance(t.op,(ast.Add,ast.Sub)):
                        stack.append((t.left,sign))
                        stack.append((t.right,sign if isinstance(t.op,ast.Add) else -sign))
                    else:
                        for m,v in rec(t).items():
                            out[m]=out.get(m,0)+sign*v
                return {m:v for m,v in out.items() if v}
            if isinstance(n.op,ast.Mult): return mul(rec(n.left),rec(n.right))
            if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant):
                return power(rec(n.left),n.right.value)
        raise ValueError(ast.dump(n))
    return rec(ast.parse(s,mode="eval").body)

def check(ok,label):
    if not ok: raise RuntimeError(label)
    CHECKS.append(label)

def load(name):
    raw=(DIR/(name+".json")).read_bytes()
    return json.loads(raw),hashlib.sha256(raw).hexdigest()

def rows(d, aliases=None): return [parse(s,aliases) for s in d["residuals"]]

def nonzero(rr): return [r for r in rr if r]

def neg(a): return scale(a,-1)

def exact_rows(a,b,label):
    check(len(a)==len(b),label+" row count")
    for i,(x,y) in enumerate(zip(a,b)):
        check(x==y,label+" row "+str(i))

def pos(prefix): return parse(f"1+{prefix}1**2+{prefix}2**2+{prefix}3*({prefix}3+1)")

def measure(d):
    vv=set(d["variables"])
    pp=set(d["fixed_numerals"])
    rr=rows(d)
    live={x for r in rr for m in r for x in m}
    check(live==vv|pp,d["name"]+" liveness")
    check(len(vv)==d["variable_count"],d["name"]+" variable count")
    degree=max(sum(x in vv for x in m) for r in rr for m in r)
    check(2*degree==d["exact_degree"],d["name"]+" symbolic degree")
    cert=d["degree_certificate"]
    r=rr[cert["residual_index_zero_based"]]
    target=tuple(sorted(x for x,e in cert["monomial"].items() for _ in range(e)))
    ports={}
    for x in pp:
        raw=gzip.decompress((TOP/"coefficients/payloads"/(x+".bin.gz")).read_bytes())
        ports[x]=int.from_bytes(raw,"little")%P
    coeff=0
    for mon,v in r.items():
        vm=tuple(x for x in mon if x in vv)
        if vm!=target: continue
        t=v%P
        for x in mon:
            if x not in vv: t=t*ports[x]%P
        coeff=(coeff+t)%P
    check(coeff!=0 and coeff==cert["actual_coefficient_mod_prime"],d["name"]+" actual leading coefficient")
    return {"variables":len(vv),"residuals":len(rr),"exact_degree":2*degree,
            "expanded_residual_terms":sum(map(len,rr))}

def main():
    packets={}; hashes={}
    for file in sorted(DIR.glob("*.json")):
        data,sha=load(file.stem)
        if "residuals" in data: packets[file.stem]=data;hashes[file.stem]=sha
    for suffix,srcname,qtext in [("","quartic40","beta*(3*J3+1)+1"),("_direct","quartic40_direct","beta*J+1")]:
        s=json.loads((TOP/"inherited/orientation70"/(srcname+".json")).read_text())
        sr=rows(s)
        C="("+qtext+"-F-alpha)"
        guard=parse(f"cone_A*F*cone_B*{C}-({qtext}-cone_A*F-cone_B*{C})**2-1-cone_pos1**2-cone_pos2**2-cone_pos3*(cone_pos3+1)")
        exact_rows(sr[:22]+[sr[24],guard],rows(packets["quartic37"+suffix]),"determinant "+suffix)
    base=packets["quartic37"]
    for label in ["sextic31","octic26","degree10_25"]:
        d=packets[label]
        aliases={k:parse(s) for k,s in d["restoration"].items()}
        old=rows(base,aliases)
        exact_rows(nonzero(old),rows(d),"literal monic restoration "+label)
        check([i for i,r in enumerate(old) if not r]==d["deleted_row_indices"],label+" deleted row identities")

    # A separate exact bridge from original quartic rows to CRT24.
    d=packets["crt_degree16_24"]
    a={}
    for name,formula in d["polynomial_abbreviations"]: a[name]=parse(formula,a)
    def ex(s): return parse(s,a)
    restore={
        "L":ex("q**2-1"),"N":ex("q**3"),"X":ex("X"),
        "C2":ex("c**2"),"F2":ex("f**2"),"Baux":ex("I**2"),
        "Delta":ex("Delta"),"D":ex("D"),"P":ex("P"),
        "zeta":ex("zeta"),"I":ex("I"),"y":ex("V+y_gap"),
        "g":ex("(V+y_gap)**2-V**2"),"tau":ex("tau+E*(c-eta)"),
        "o":ex("c*T-f*R"),
    }
    transformed=rows(base,restore)
    nr=rows(d)
    # These rows now retain their original a-based lifts. Once a is
    # eliminated by a=E+Y, they become E-X*Y and c-k*Y-eta exactly.
    exact_rows([transformed[3],transformed[4],transformed[5]],
               [nr[1],nr[2],nr[3]],
               "three retained a-based lift rows")
    for oi,ni in [(7,4),(11,5),(20,6),(21,7),(13,8),(22,9),(23,10),(15,0)]:
        check(transformed[oi]==nr[ni],f"CRT24 old row {oi} to new row {ni}")
    for oi in [0,1,2,6,8,9,10,12,14,17,18,19]:
        check(not transformed[oi],f"CRT24 restored definition {oi}")
    check(transformed[16]==ex("V-c*j+R"),"sole old auxiliary congruence handled by CRT lemma")

    # Exact successive monic projections, then the parity-forced half-center.
    previous="crt_degree16_24"
    for name,var,expr in [("crt_degree26_23","V","Vcrt"),("crt_degree26_22","a","E+Y"),("crt_degree28_21","E","X*Y")]:
        old=packets[previous];new=packets[name]
        env={}
        for n,f in old["polynomial_abbreviations"]: env[n]=parse(f,env)
        mapped=rows(old,{var:parse(expr,env)})
        exact_rows(nonzero(mapped),rows(new),"successive projection "+name)
        previous=name
    old=packets[previous];new=packets["crt_degree44_20"]
    env={}
    for n,f in old["polynomial_abbreviations"]:env[n]=parse(f,env)
    eta=parse("c-k*Y",env)
    half_tau=scale(add(parse("tau"),parse("k",env)),Fraction(1,2))
    mapped=nonzero(rows(old,{"eta":eta,"tau":half_tau}))
    mapped[0]=scale(mapped[0],4)
    exact_rows(mapped,rows(new),"half-centered eta elimination")
    parity=parse("tau**2+2*tau*(2*P-k)+k**2-4")
    check(add(parity,neg(parse("(tau-k)**2")))==parse("4*tau*P-4"),"half-center parity multiple of four")

    # Read the expanded packet only after independently expanding its
    # human-readable definitions and formulas.
    for name,d in packets.items():
        if "factored_residuals" in d:
            env={}
            for n,f in d["polynomial_abbreviations"]:env[n]=parse(f,env)
            exact_rows([parse(f,env) for f in d["factored_residuals"]],rows(d),"readable formula "+name)
    for name,d in packets.items():
        if d.get("guard_transformation")!="package68 nearest-square pairing" and d.get("guard_transformation")!="package68 nearest-square pairing of determinant and eta*zeta":
            continue
        par=packets[Path(d["parent"]).stem];pr=rows(par)
        Z=add(pr[-2],pos("eta_zeta_pos"));G=add(pr[-1],pos("cone_pos"))
        inside=add(add(parse("pair_root**2+1"),neg(G)),neg(Z))
        pair=add(add(mul(G,Z),neg(power(inside,2))),neg(pos("pair_pos")))
        exact_rows(pr[:-2]+[pair],rows(d),"nearest-square guard "+name)

    measurements={name:measure(d) for name,d in packets.items()}
    out={"status":"PASS","checks":len(CHECKS),"scope":"Exact polynomial identities, source bridges, liveness and actual-slice degree certificates; no end-to-end kernel certificate.",
         "packet_sha256":hashes,"metrics":measurements,"check_labels":CHECKS}
    (TOP/"certificates/INDEPENDENT_INTEGER_AUDIT.json").write_text(json.dumps(out,indent=2)+"\n")
    print(json.dumps({"status":"PASS","checks":len(CHECKS),"metrics":measurements},indent=2))

if __name__=="__main__":main()
