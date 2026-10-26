#!/usr/bin/env python3
"""Two exact source-coordinate factorizations; no semantic change to P83."""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json

HERE=Path(__file__).resolve().parent

def dump(path,obj):path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n')
def C(k):return ['c',k]
def V(j):return ['v',j]
def add(*xs):
    r=C(0)
    for x in xs:r=['+',r,x]
    return r
def mul(*xs):
    r=C(1)
    for x in xs:r=['*',r,x]
    return r
def sq(x):return mul(x,x)
def minus(x,y):return add(x,mul(C(-1),y))

def formulas():
    # H is twice the half-integral square center suggested by the expanded
    # rows. All coefficients here are ordinary integers.
    weighted=[(1,8),(1,9),(4,19),(2,22),(4,24),(2,27),(2,29),
              (4,30),(2,32),(2,34),(4,36),(2,37),(2,40),(2,44),(4,65),(2,66)]
    H=add(*(mul(C(c),V(j)) for c,j in weighted))
    h2=sq(H)
    q=add(C(3),mul(C(6),V(220)))
    quad=add(sq(V(0)),sq(add(V(0),V(4))),
             *(sq(V(j)) for j in [1,2,10,11,12,13,14,15,16,17,103,121,127,195]))
    negative=[145,153,158,161,164,167,170,173,177,180,183,187,190,214,215,216]
    N=add(sq(V(193)),mul(C(2),V(158)),mul(C(-1),V(216)),
          *(mul(C(-1),sq(V(j))) for j in negative))
    inner=add(quad,mul(C(-2),V(8)),mul(C(4),V(225),add(V(225),C(1))),sq(q),C(4))
    large=add(mul(q,inner),
        mul(C(2),add(C(1),mul(C(3),V(220))),add(h2,sq(V(8)),sq(V(9)))),
        mul(C(-2),V(8),V(9)),V(19),N,C(-3))
    residual=add(N,C(-1),mul(C(-1),V(19)),mul(C(-1),h2),sq(add(V(8),V(9))))
    return {'restored_coordinate':139,'restoration':large,
            'source_residual_row':170,'residual':residual,
            'shared_H':H,'shared_N':N}

class Graph:
    def __init__(self):self.nodes=[];self.memo={}
    def put(self,t):
        t=tuple(t)
        if t not in self.memo:self.memo[t]=len(self.nodes);self.nodes.append(list(t))
        return self.memo[t]
    def c(self,n):return self.put(('const',n))
    def op(self,op,a,b):
        x,y=self.nodes[a],self.nodes[b]
        if x[0]==y[0]=='const':return self.c(x[1]+y[1] if op=='add' else x[1]*y[1])
        if op=='add':
            if x==['const',0]:return b
            if y==['const',0]:return a
        else:
            if x==['const',0] or y==['const',0]:return self.c(0)
            if x==['const',1]:return b
            if y==['const',1]:return a
        return self.put((op,min(a,b),max(a,b)))

def build(source,projection,formula):
    g=Graph();free=projection['free'];roots={v:g.put(('input',i)) for i,v in enumerate(free)}
    definitions={p['variable']:p['restoration'] for p in projection['pivots']}
    active=set()
    def expr(ast):
        op=ast[0]
        if op=='c':return g.c(ast[1])
        if op=='v':return coordinate(ast[1])
        return g.op('add' if op=='+' else 'mul',expr(ast[1]),expr(ast[2]))
    def sparse(terms):
        out=g.c(0)
        for coefficient,monomial in terms:
            term=g.c(coefficient)
            for v in monomial:term=g.op('mul',term,coordinate(v))
            out=g.op('add',out,term)
        return out
    def coordinate(v):
        if v in roots:return roots[v]
        if v in active:raise ValueError('cycle')
        active.add(v)
        roots[v]=expr(formula['restoration']) if v==139 else sparse(definitions[v])
        active.remove(v)
        return roots[v]
    residuals=[]
    for row in projection['retained_rows']:
        residuals.append(expr(formula['residual']) if row==170 else sparse(source['residuals'][row]['terms']))
    out=g.c(0)
    for root in residuals:out=g.op('add',out,g.op('mul',root,root))
    restored=[coordinate(v) for v in range(len(source['variables']))]
    return {'schema':'ordinary_integer_polynomial_dag_v1','domain':'unrestricted integers',
            'variables':[source['variables'][v]['name'] for v in free],
            'nodes':g.nodes,'residual_roots':residuals,'source_coordinate_roots':restored,'output':out}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--canonical-dir',type=Path,default=HERE.parent)
    parser.add_argument('--check',action='store_true');args=parser.parse_args();canonical=args.canonical_dir
    source=json.loads((canonical/'source227.json').read_text());projection=json.loads((canonical/'P83/projection.json').read_text())
    f=formulas();e=build(source,projection,f)
    nodes=e['nodes'];live={e['output']}
    for j in range(len(nodes)-1,-1,-1):
        if j in live and nodes[j][0] in ('add','mul'):live.update(nodes[j][1:])
    metrics={'variables':len(e['variables']),'residuals':len(e['residual_roots']),
             'live_binary_gates':sum(nodes[j][0] in ('add','mul') for j in live),
             'live_nodes':len(live),'total_nodes_with_restorations':len(nodes),
             'largest_absolute_literal':max(abs(nodes[j][1]) for j in live if nodes[j][0]=='const'),
             'operation_breakdown':dict(Counter(nodes[j][0] for j in live if nodes[j][0] in ('add','mul')))}
    for name,obj in [('factorizations.json',f),('circuit.json',e),('METRICS.json',metrics)]:
        data=(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n').encode()
        if args.check:
            if (HERE/name).read_bytes()!=data:raise ValueError('Byte rebuild differs: '+name)
        else:(HERE/name).write_bytes(data)
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':main()
