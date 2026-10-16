#!/usr/bin/env python3
"""Exact symbolic wrapper counts; these are NOT Turing-machine state counts.

Source14 comparison uses its displayed uncurried EPSC wrapper, matrix atom
cost one, variable labels/payloads and parameter closure excluded. EFPC is the
exact seeded fixed-point normal form developed in this report.  Distinct-DAG
counts measure identical named-syntax subtrees, not compiler sharing.
"""
import json
from collections import Counter
from pathlib import Path

def mem(i,j): return ("mem",i,j)
def imp(a,b): return ("imp",a,b)
def all_(i,a): return ("all",i,a)
def not_(a): return ("not",a)
def and_(a,b): return not_(imp(a,not_(b)))
def or_(a,b): return imp(not_(a),b)
def ex(i,a): return not_(all_(i,not_(a)))
def iff(a,b): return ("iff",a,b)

def wrapper(kind):
    x,y,b,c,z=range(5)
    rho=("matrix",x,y)
    bound=all_(x,ex(b,all_(y,imp(rho,all_(z,imp(mem(z,y),mem(z,b)))))))
    seed=all_(z,not_(mem(z,x)))
    active=and_(or_(seed,mem(x,c)),rho)
    if kind=="EPSC":
        closed=all_(x,all_(y,imp(active,mem(y,c))))
        support=all_(y,imp(mem(y,c),ex(x,rho)))
        body=and_(closed,support)
    elif kind=="EFPC":
        body=all_(y,iff(mem(y,c),ex(x,active)))
    else: raise ValueError(kind)
    return imp(bound,ex(c,body))

def transform(f,mode):
    op=f[0]
    if op in ("mem","matrix","bot"): return f
    if op=="imp": return imp(transform(f[1],mode),transform(f[2],mode))
    if op=="all": return all_(f[1],transform(f[2],mode))
    if op=="iff":
        if mode=="primitive_iff":return iff(transform(f[1],mode),transform(f[2],mode))
        return transform(and_(imp(f[1],f[2]),imp(f[2],f[1])),mode)
    if op!="not":raise ValueError(op)
    a=transform(f[1],mode)
    if mode=="bottom":return imp(a,("bot",))
    if mode=="cancel" and a[0]=="not":return a[1]
    return not_(a)

def children(f):
    if f[0] in ("mem","matrix","bot"):return ()
    if f[0]=="not":return (f[1],)
    if f[0]=="all":return (f[2],)
    return f[1:]

def metrics(f):
    counts=Counter();unique=set()
    def visit(g):
        counts[g[0]]+=1;unique.add(g)
        for h in children(g):visit(h)
    visit(f)
    return {"tree_nodes":sum(counts.values()),"distinct_subtrees":len(unique),
            "matrix_occurrences":counts["matrix"],"constructor_counts":dict(sorted(counts.items()))}

def main():
    result={kind:{mode:metrics(transform(wrapper(kind),mode))
             for mode in ("unary","cancel","bottom","primitive_iff")}
            for kind in ("EPSC","EFPC")}
    assert [result["EPSC"][mode]["tree_nodes"] for mode in ("unary","cancel","bottom")]==[39,37,51]
    out={"scope":"symbolic syntax only; no machine-state claim", "metrics":result}
    print(json.dumps(out,indent=2))

if __name__=="__main__": main()
