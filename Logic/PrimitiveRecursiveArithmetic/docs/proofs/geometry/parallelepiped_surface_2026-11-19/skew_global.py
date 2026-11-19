#!/usr/bin/env python3
"""Exact global verification of the nonvertex skew diameter. Requires SymPy and libz3."""
import ctypes
from ctypes.util import find_library
from itertools import product
import sympy as s
from antipodal_check import Q, position
from fixed_exact import add, base, det, gram_matrix, mul, norm2, sub, unfold

u,v,t=s.symbols("u v t")
g=gram_matrix(("1","1","4","0","80/401","0"))
axis_pairs=((1,2),(0,2),(0,1))


def pol(p):
    """SMT polynomial, scaled by a positive integer so all coefficients are integral."""
    poly=s.Poly(p,u,v,t)
    terms=poly.clear_denoms()[1].terms()
    parts=[]
    for powers,k in terms:
        factors=[str(sym) for sym,n in zip((u,v,t),powers) for _ in range(n)]
        k=int(k)
        coeff=str(k) if k>=0 else f"(- {-k})"
        if k!=1 or not factors:
            factors.insert(0,coeff)
        parts.append(factors[0] if len(factors)==1 else "(* "+" ".join(factors)+")")
    return parts[0] if len(parts)==1 else "(+ "+" ".join(parts)+")"


def cond(op,expr):
    z=s.expand(expr)
    if z.is_number:
        return str(bool(z>0 if op==">" else z>=0)).lower()
    return f"({op} {pol(z)} 0)"


def symbolic_routes(axis, collect_inequalities=False):
    axes=axis_pairs[axis]
    p=[0]*3
    for i,k in enumerate(axes):
        p[k]=(u,v)[i]
    q=[1-x for x in p]
    origin=(Q(0),Q(0))
    start=position(origin,base(g,axis),p)
    rows=[]
    def visit(path,org,vec,gates):
        a,bit=path[-1]
        if (a,bit)==(axis,1):
            end=position(org,vec,q); d=sub(end,start)
            prev=None; tests=[]; inequalities=[]
            for low,high,sign in gates:
                w=sub(high,low); w0=sub(low,start)
                b=s.expand(sign*det(d,w)); A=s.expand(sign*det(w0,w)); C=s.expand(sign*det(w0,d))
                inequalities.extend([b,A,b-A,C,b-C])
                tests.extend([cond(">",b),cond(">=",A),cond(">=",b-A),
                              cond(">=",C),cond(">=",b-C)])
                if prev is not None:
                    aa,bb=prev
                    inequalities.append(A*bb-aa*b)
                    tests.append(cond(">=",A*bb-aa*b))
                prev=A,b
            tests=list(dict.fromkeys(q for q in tests if q!="true"))
            guard="false" if "false" in tests else "(and "+" ".join(tests)+")"
            rows.append((path,s.expand(norm2(d)),(guard,inequalities) if collect_inequalities else guard)); return
        for j,new_bit in product(range(3),(0,1)):
            if j==a or (j,new_bit) in path:
                continue
            no,nv,(left,right)=unfold(g,a,bit,org,vec,j,new_bit)
            middle=position(org,vec,[Q(1,2)]*3)
            sign=1 if det(sub(right,left),sub(middle,left))>0 else -1
            visit(path+[(j,new_bit)],no,nv,gates+[(left,right,sign)])
    visit([(axis,0)],origin,base(g,axis),[])
    return rows


def solve(smt):
    lib=ctypes.CDLL(find_library("z3"))
    def bind(name,res,*args):
        f=getattr(lib,name); f.restype=res; f.argtypes=args; return f
    ptr=ctypes.c_void_p
    cfg=bind("Z3_mk_config",ptr)()
    ctx=bind("Z3_mk_context",ptr,ptr)(cfg)
    run=bind("Z3_eval_smtlib2_string",ctypes.c_char_p,ptr,ctypes.c_char_p)
    ans=run(ctx,smt.encode()).decode().strip()
    bind("Z3_del_context",None,ptr)(ctx)
    bind("Z3_del_config",None,ptr)(cfg)
    return ans


def check(label,constraints):
    text="(set-logic QF_NRA)\n(declare-const u Real)\n(declare-const v Real)\n"
    text+="\n".join("(assert "+c+")" for c in constraints)+"\n(check-sat)\n"
    ans=solve(text)
    print(label,ans,flush=True)
    assert ans=="unsat",label


def main(check_smt=True):
    cutoff=s.Rational(183,20)  # 9.15
    domain=["(> u 0)","(< u 1)","(> v 0)","(< v 1)"]
    for axis in range(3) if check_smt else ():
        rows=symbolic_routes(axis)
        restrictions=list(domain)
        if axis==2:
            restrictions+=["(>= v (/ 1 2))","(not (and (>= u (/ 1 4)) (<= u (/ 1 2)) (>= v (/ 3 5)) (<= v (/ 4 5))))"]
        for path,f,guard in rows:
            if len(path)<=4 and guard!="false":
                restrictions.append("(or (not "+guard+") "+cond(">",f-cutoff)+")")
        check("Above 9.15 outside candidate region on face "+str(axis),restrictions)
    rows=symbolic_routes(2)
    local=["(>= u (/ 1 4))","(<= u (/ 1 2))","(>= v (/ 3 5))","(<= v (/ 4 5))"]
    for i in (2,6,20) if check_smt else ():
        check("Active word legal throughout region "+str(i),local+["(not "+rows[i][2]+")"])
    f2,f6,f20=[rows[i][1] for i in (2,6,20)]
    for label,expr in [('increasing f6 in v',s.diff(f6,v)),('decreasing f20 in u',-s.diff(f20,u)),
                       ('increasing f2 in u',s.diff(f2,u)),('decreasing f2 in v',-s.diff(f2,v))]:
        if check_smt: check(label,local+["(not "+cond(">",expr)+")"])
    eqs=[s.Poly(f-t,u,v,t).clear_denoms()[1].as_expr() for f in (f6,f20,f2)]
    basis=s.groebner(eqs,u,v,t,order="lex")
    prim=[p.as_expr() for p in basis.polys]
    poly=s.Poly(prim[-1],t)
    lo=s.Rational(915266,100000); hi=s.Rational(915268,100000)
    assert poly.count_roots(lo,hi)==1
    # Test every word at the algebraic candidate. For the lower bound it is
    # enough to exclude even inadmissible words when their costs are >= T.
    pstar=[s.cancel(-f.subs(x,0)/f.coeff(x)) for x,f in zip((u,v),prim[:2])]
    def nonnegative(expr):
        r=s.Poly(s.expand(expr).subs(dict(zip((u,v),pstar))),t).rem(poly)
        if r.is_zero: return True
        a,b=lo,hi
        for _ in range(128):
            low=high=s.Rational(0)
            for (k,),c in r.terms():
                one,two=c*a**k,c*b**k
                low+=min(one,two);high+=max(one,two)
            if low>0:return True
            if high<0:return False
            m=(a+b)/2
            if poly.count_roots(a,m):b=m
            else:a=m
        raise ArithmeticError("root sign undecided within 128 bisections")
    assert all(nonnegative(expr) for expr in (u-s.Rational(1,4),s.Rational(1,2)-u,
                                                v-s.Rational(3,5),s.Rational(4,5)-v))
    assert all(nonnegative(f-t) for path,f,guard in rows)
    assert all(s.Poly((f-t).subs(dict(zip((u,v),pstar))),t).rem(poly).is_zero
               for f in (f6, f20, f2))
    print("All 28 squared word lengths are at least T. The three local costs equal T.",flush=True)
    print("Defining equations (u,v,T)",prim,flush=True)
    print("D^2 = unique root in",lo,hi,"numerical",s.nroots(poly)[0],flush=True)


if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--algebra-only",action="store_true",help="Use with rational_cover.py for verification without libz3")
    main(not parser.parse_args().algebra_only)
