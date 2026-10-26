#!/usr/bin/env python3
"""Sparse constructor compiler with exact acyclic gate definitions."""
import json,sys,copy,hashlib,math,functools
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'helpers'))
from polynomial import add,scale,sub,mul,const,var,terms,poly,degree,canonical,compact,expand,subst

class Builder:
    def __init__(self,variables):
        self.variables=variables;self.rows=[];self.memo={};self.ops=[]
    def wire(self,p,name=None,target=None):
        if degree(p)<=1 and target is None:return p
        if target is None:
            quad={m:c for m,c in p.items() if len(m)==2}
            linear={m:c for m,c in p.items() if len(m)<2}
            g=functools.reduce(math.gcd,map(abs,quad.values()))
            if quad[min(quad)]<0:g=-g
            norm={m:c//g for m,c in quad.items()}
            key=tuple(sorted(norm.items()))
            if key in self.memo:
                oldg,oldlinear,oldvar=self.memo[key]
                if g%oldg==0:
                    ratio=g//oldg
                    return add(linear,scale(-ratio,oldlinear),scale(ratio,oldvar))
            target=len(self.variables)
            self.variables.append({'name':name or 'sparse.local.%d'%len(self.rows),'kind':'gate'})
            self.rows.append({'label':name or 'sparse.local.definition','terms':terms(sub(var(target),p))})
            self.memo[key]=(g,linear,var(target))
            return var(target)
        key=tuple(sorted(p.items()))
        if target is None and key in self.memo:return self.memo[key]
        if degree(p)>2:raise ValueError(('degree',degree(p)))
        if target is None:
            target=len(self.variables)
            self.variables.append({'name':name or 'sparse.local.%d'%len(self.rows),'kind':'gate'})
        self.rows.append({'label':name or 'sparse.local.definition','terms':terms(sub(var(target),p))})
        ans=var(target);self.memo[key]=ans
        return ans
    def product(self,a,b,name=None):return self.wire(mul(a,b),name)
    def square(self,a):return self.product(a,a)

def generate(style='sparse'):
    inp=ROOT/'source/parent216.json';old=json.loads(inp.read_text())
    vs=copy.deepcopy(old['variables']);b=Builder(vs)
    a,beta,c,d=add(var(8),const(-1)),var(9),var(10),var(11)
    def base(x,y):return add(b.square(add(x,y)),x)
    if style=='sparse':
        def I(x,y):return scale(4,base(x,y))
        def M(x,y):return add(I(x,y),const(1))
        def A(x,y):return add(I(x,y),const(2))
        def E(x,y):return add(I(x,y),const(3))
    elif style=='shell':
        def I(x,y):return scale(2,base(x,y))
        def M(x,y):return add(I(x,y),const(1))
        def A(x,y):return scale(2,add(b.square(add(x,y)),scale(3,x),scale(4,y),const(3)))
        def E(x,y):return add(A(x,y),const(1))
    else:raise ValueError(style)
    def N(x):return I(x,const(1))
    def X(x,y):return N(A(x,N(y)))
    def req(x,k,h):return A(x,I(h,N(A(x,I(h,N(M(x,k)))))))
    def clos(x,y,k,h):
        s=A(k,I(M(k,x),M(k,y)))
        tail=I(s,req(y,k,h));tail=N(A(x,tail));tail=N(A(x,I(h,tail)))
        return A(y,I(M(y,k),tail))
    def bundle(x,y,z):
        nks=A(z,I(clos(x,y,z,z),N(req(y,z,z))))
        vrel=I(M(x,y),A(z,M(x,y)))
        return N(I(vrel,nks))
    codes=[X(a,E(a,beta)),I(A(a,I(beta,c)),I(A(a,beta),A(a,c))),
        I(E(a,beta),I(M(c,a),M(c,beta))),I(A(a,A(beta,c)),A(beta,A(a,c))),
        I(E(c,a),I(M(c,beta),M(a,beta))),I(X(a,A(a,beta)),beta),
        I(E(c,a),I(E(c,beta),A(M(a,beta),E(a,beta)))),
        I(I(I(c,d),a),I(I(a,c),I(beta,c))),bundle(a,beta,c)]
    code_rows=len(b.rows)
    F,S,Sp=var(2),var(12),var(13)
    FSp=b.product(F,Sp,'local.FSp')
    FS=b.product(F,S,'local.FS')
    gap=sub(S,Sp)
    factors=[gap]+[b.wire(sub(gap,mul(FSp,h)),'local.axiom_factor%d'%j) for j,h in enumerate(codes[:-1])]
    guard=b.product(sub(c,a),sub(c,beta),'local.guard_product')
    gd=b.wire(sub(mul(guard,guard),mul(add(d,const(1)),add(d,const(1)))),'local.guard_defect')
    bd=b.wire(sub(gap,mul(FSp,codes[-1])),'local.bundle_factor')
    joint=b.wire(add(mul(gd,gd),mul(bd,bd)),'local.joint',79)
    mp0=b.wire(add(const(1),mul(F,I(a,beta))),'local.mp0')
    mp1=b.wire(add(S,mul(a,FS)),'local.mp1')
    mp=b.wire(sub(add(Sp,mul(beta,FSp)),mul(mp0,mp1)),'local.mp')
    gen=b.wire(sub(add(S,mul(beta,FS)),add(Sp,mul(FSp,A(a,beta)))),'local.gen')
    factors += [mp,gen]
    product=factors[0]
    for h in factors[1:]:product=b.product(product,h,'local.axis_product')
    axis=b.wire(mul(product,product),'local.axis_square',95)
    # The only old syntax coordinates crossing this cut are joint and axis_square.
    kept=[]
    for j,r in enumerate(old['residuals']):
        if 4<=j<=80:continue
        if r['label']=='multiplication' and poly(r['terms'])==sub(var(207),mul(F,S)):
            continue
        kept.append(copy.deepcopy(r))
    eq=copy.deepcopy(old)
    eq['variables']=vs;eq['residuals']=kept+b.rows
    eq['schema']='sparse-constructor-graft-v1'
    final,ren=compact(eq)
    pol=expand(final)
    metrics={'style':style,'variables':len(final['variables']),'rows':len(final['residuals']),
        'local_code_rows':code_rows,'local_rows':len(b.rows),'degree':degree(pol),
        'monomials':len(pol),'height':max(map(abs,pol.values()))}
    graft={'base_sha256':hashlib.sha256(inp.read_bytes()).hexdigest(),
        'code_polynomials_before_compact':[terms(x) for x in codes],
        'new_rows':b.rows,'renumbering':[[i,j] for i,j in ren.items()]}
    return final,graft,metrics
