#!/usr/bin/env python3
"""Portable straight-line evaluators and exact comparison to residual packets."""
from pathlib import Path
import json
from collections import Counter
from polynomial import Poly, parse, require

ROOT = Path(__file__).resolve().parent


class Graph:
    def __init__(self):
        self.nodes = []
        self.cache = {}

    def intern(self, key, record):
        if key not in self.cache:
            self.cache[key] = len(self.nodes)
            self.nodes.append(record)
        return self.cache[key]

    def const(self, value):
        return self.intern(('const', value), {'op':'const', 'value':value})

    def var(self, value):
        return self.intern(('symbol', value), {'op':'symbol', 'name':value})

    def op(self, op, a, b):
        if op in {'add','mul'} and a > b:
            a,b = b,a
        an,bn = self.nodes[a],self.nodes[b]
        if an['op'] == bn['op'] == 'const':
            av,bv = an['value'],bn['value']
            return self.const({'add':lambda:av+bv, 'sub':lambda:av-bv,
                               'mul':lambda:av*bv}[op]())
        if op == 'mul':
            if any(n['op']=='const' and n['value']==0 for n in [an,bn]):
                return self.const(0)
            if an['op']=='const' and an['value']==1:return b
            if bn['op']=='const' and bn['value']==1:return a
        if op == 'add':
            if an['op']=='const' and an['value']==0:return b
            if bn['op']=='const' and bn['value']==0:return a
        if op == 'sub':
            if a==b:return self.const(0)
            if bn['op']=='const' and bn['value']==0:return a
        return self.intern((op,a,b), {'op':op, 'args':[a,b]})

    def add(self,a,b):return self.op('add',a,b)
    def sub(self,a,b):return self.op('sub',a,b)
    def mul(self,a,b):return self.op('mul',a,b)
    def sq(self,a):return self.mul(a,a)

    def live(self, outputs):
        seen=set()
        def visit(i):
            if i not in seen:
                seen.add(i)
                for j in self.nodes[i].get('args',[]):visit(j)
        for i in outputs:visit(i)
        ids=sorted(seen); mapping={v:i for i,v in enumerate(ids)}
        nodes=[]
        for i in ids:
            row=dict(self.nodes[i])
            if 'args' in row:row['args']=[mapping[j] for j in row['args']]
            nodes.append(row)
        return nodes,[mapping[i] for i in outputs]


def build(name):
    source=json.loads((ROOT/(name+'.json')).read_text())
    g=Graph(); a=g.add; s=g.sub; m=g.mul; sq=g.sq
    sy={n:g.var(n) for n in source['variables']+source['fixed_numerals']}
    J,F,alpha,f,h,r,v_scale,tau,eta,y,gamma,o,j,E,c,av,u,Z,beta,K0,MC,MF,cone_A,cone_B = (
        sy[n] for n in ['J','F','alpha','f','h','r','v_scale','tau','eta','y',
                        'gamma','o','j','E','c','a','u','Z','beta','K0','MC',
                        'MF','cone_A','cone_B'])
    direct = name in {'degree12_23','degree10_24','degree14_22'}
    no_zeta = name in {'degree12_25','degree12_23','degree14_22'}
    centered = name in {'degree10_24','degree14_22'}
    n0,n1,n2,n3,n4=(g.const(i) for i in range(5))
    qb=m(beta,J); q=a(qb,n1); C=s(s(q,F),alpha)
    hE=m(h,E); jc=m(j,c)
    fo=m(f,o)
    V=s(fo,c) if direct else sy['V']
    if no_zeta:
        idx=s(jc,V); k=a(a(idx,n1),hE); zeta=s(k,eta)
    else:
        zeta=sy['zeta']; k=a(eta,zeta); idx=s(s(k,n1),hE)
    H=a(m(n4,av),n3)
    ac=m(av,c); gamH=m(gamma,H)
    if direct:
        X=m(m(n4,q),sq(u)); D=a(a(X,ac),gamH)
    else:
        D=sy['D']; X=s(s(D,ac),gamH)
    c2=sq(c); f2=sq(f); y2=sq(y); V2=sq(V)
    ae=s(av,E); cm=s(c,eta)
    vv=a(m(n2,v_scale),n1); rr=a(m(n2,r),n1)
    I=m(rr,c2) if name=='degree14_22' else sy['I']
    I2=sq(I)
    if name=='sextic31':
        L=sy['L']; Delta=sy['Delta']; Baux=sy['Baux']
        N=m(q,a(L,n1))
    else:
        q2=sq(q); L=s(q2,n1); N=m(q,q2)
        Delta=a(sq(av),H); Baux=I2
    R=a(m(a(m(qb,s(q,F)),alpha),L),m(a(MC,m(q,MF)),J))
    # Residual order agrees literally with the algebraic builder.
    rows=[]
    if name=='sextic31':rows.append(s(L,s(sq(q),n1)))
    rows += [s(ae,m(vv,N)), s(E,m(X,ae)), s(cm,m(ae,k)),
             s(a(sq(tau),m(s(m(n2,tau),k),m(E,cm))),n1)]
    if name=='sextic31':rows.append(s(Delta,a(sq(av),H)))
    if name=='degree10_24':
        b=a(ac,gamH)
        main=a(m(E,a(X,m(n2,b))),
               m(ae,s(m(H,s(m(gamma,a(m(n2,ac),gamH)),c2)),n1)))
    else:
        main=s(s(sq(D),m(Delta,c2)),n1)
    rows += [main,s(idx,R),
             s(s(m(a(m(K0,q),X),C),m(q,F)),m(Z,qb))]
    if not direct:rows.append(s(a(V,c),fo))
    if not no_zeta:rows.append(s(a(idx,V),jc))
    if name!='degree14_22':rows.append(s(I,m(rr,c2)))
    if name=='sextic31':rows.append(s(Baux,I2))
    strong_right=m(Delta,s(f2,n1))
    rows.append(s(Baux,strong_right))
    if centered:
        aux_scale=strong_right if name=='degree14_22' else Baux
        gap_product=m(a(c,y),s(a(m(n2,fo),y),c))
        auxiliary=s(s(sq(a(fo,y)),m(aux_scale,gap_product)),n1)
    else:
        auxiliary=s(s(y2,m(Baux,s(y2,V2))),n1)
    rows.append(auxiliary)
    if not direct:rows.append(s(X,m(m(n4,q),sq(u))))
    U=m(cone_A,F); Vn=m(cone_B,C)
    det=s(m(U,Vn),sq(s(s(q,U),Vn)))
    ez=m(eta,zeta)
    def pos(prefix):
        p1,p2,p3=(sy[prefix+str(i)] for i in range(1,4))
        return a(a(a(n1,sq(p1)),sq(p2)),m(p3,a(p3,n1)))
    if name=='sextic31':
        rows += [s(det,pos('cone_pos')),s(ez,pos('eta_zeta_pos'))]
    else:
        root=sy['pair_root']
        center=a(s(s(sq(root),det),ez),n1)
        pair=s(m(det,ez),sq(center))
        rows.append(s(pair,pos('pair_pos')))
    output=g.const(0)
    for row in rows:output=a(output,sq(row))
    nodes,outputs=g.live(rows+[output])
    values=[]
    for node in nodes:
        if node['op']=='const':p=Poly.integer(node['value'])
        elif node['op']=='symbol':p=Poly.symbol(node['name'])
        else:
            left,right=(values[i] for i in node['args'])
            p={'add':lambda:left+right,'sub':lambda:left-right,
               'mul':lambda:left*right}[node['op']]()
        values.append(p)
    require([values[i] for i in outputs[:-1]] == [parse(x) for x in source['residuals']],
            name+': every compact circuit residual equals its exact packet')
    counts=Counter(node['op'] for node in nodes if node['op'] in {'add','sub','mul'})
    data={'name':name, 'nodes':nodes, 'residual_outputs':outputs[:-1],
          'output':outputs[-1], 'binary_operation_counts':dict(sorted(counts.items())),
          'total_binary_operations':sum(counts.values()),
          'variables':source['variables'], 'fixed_numerals':source['fixed_numerals'],
          'coefficient_binding':'coefficients/BINDING.json',
          'count_convention':'live binary +,-,* gates, including scalar products and squares; exact fixed inputs and reference reuse free; constant-only small integer arithmetic folded; syntactically identical commutative gates shared',
          'not_claimed':'minimum circuit size or bit-operation complexity'}
    (ROOT/(name+'_circuit.json')).write_text(json.dumps(data,indent=2)+'\n')
    return {'name':name,'operations':sum(counts.values()),'counts':dict(counts),
            'exact_residual_identity':'PASS'}


if __name__=='__main__':
    results=[build(name) for name in ['sextic31','octic26','degree10_24',
                                     'degree12_25','degree12_23','degree14_22']]
    (ROOT/'CIRCUIT_CHECKS.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
