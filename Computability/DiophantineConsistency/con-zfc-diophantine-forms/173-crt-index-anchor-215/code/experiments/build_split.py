#!/usr/bin/env python3
"""Research compiler for a fixed-role seed and a separate vacuity schema."""
from pathlib import Path
from collections import defaultdict
import json, copy, argparse, hashlib

ROOT=Path(__file__).resolve().parents[2]

def add(*ps):
    z=defaultdict(int)
    for p in ps:
        for m,c in p.items(): z[m]+=c
    return {m:c for m,c in z.items() if c}
def scale(k,p): return {m:k*c for m,c in p.items() if k*c}
def sub(p,q): return add(p,scale(-1,q))
def mul(p,q):
    z=defaultdict(int)
    for m,c in p.items():
        for n,d in q.items(): z[tuple(sorted(m+n))]+=c*d
    return {m:c for m,c in z.items() if c}
def const(c): return {():c} if c else {}
def var(i): return {(i,):1}
def terms(p): return [[c,list(m)] for m,c in sorted(p.items())]
def poly(ts): return {tuple(m):c for c,m in ts}
def canonical(x): return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def subst(p,i,q):
    out={}
    for m,c in p.items():
        a=const(c)
        for j in m: a=mul(a,q if j==i else var(j))
        out=add(out,a)
    return out
def degree(p): return max(map(len,p),default=0)

class Builder:
    def __init__(self,variables):
        self.variables=variables
        self.rows=[]
        self.cache={}
        self.ledger=[]
    def gate(self,p,name):
        if degree(p)<=1:return p
        if degree(p)>2:raise ValueError(('high gate',name))
        key=tuple(sorted(p.items()))
        if key in self.cache:return var(self.cache[key])
        i=len(self.variables)
        self.variables.append({'name':'split.'+name,'kind':'gate'})
        self.rows.append({'label':'split.'+name,'terms':terms(sub(var(i),p))})
        self.ledger.append({'coordinate':i,'name':name,'expression':terms(p)})
        self.cache[key]=i
        return var(i)
    def product(self,p,q,name):return self.gate(mul(p,q),name)
    def square(self,p,name):return self.product(p,p,name)
    def record(self,p,name):
        self.rows.append({'label':'split.'+name,'terms':terms(p)})
    def square_sum(self,x,y):return self.square(add(x,y),'square.'+str(len(self.ledger)))
    def I(self,x,y):return scale(2,add(self.square_sum(x,y),x))
    def M(self,x,y):return add(self.I(x,y),const(1))
    def A(self,x,y):return scale(2,add(self.square_sum(x,y),scale(3,x),scale(4,y),const(3)))
    def E(self,x,y):return add(self.A(x,y),const(1))
    def N(self,x):return self.I(x,const(1))
    def X(self,x,y):return self.N(self.A(x,self.N(y)))
    def req(self,b,k,m):
        tail=self.N(self.M(b,k))
        tail=self.N(self.A(b,self.I(m,tail)))
        return self.A(b,self.I(m,tail))
    def clos(self,a,b,k,m):
        s=self.A(k,self.I(self.M(k,a),self.M(k,b)))
        tail=self.I(s,self.req(b,k,m))
        tail=self.N(self.A(a,tail))
        tail=self.N(self.A(a,self.I(m,tail)))
        return self.A(b,self.I(self.M(b,k),tail))

def make_local(variables, mode='split'):
    b=Builder(variables)
    I,M,A,E,N,X=b.I,b.M,b.A,b.E,b.N,b.X
    a=add(var(9),const(-1));bb=var(10);c=var(11);d=var(12)
    S,Sp,F=var(13),var(14),var(2)
    codes=[X(a,E(a,bb)),I(A(a,I(bb,c)),I(A(a,bb),A(a,c))),
      I(E(a,bb),I(M(c,a),M(c,bb))),I(A(a,A(bb,c)),A(bb,A(a,c))),
      I(E(c,a),I(M(c,bb),M(a,bb))),I(X(a,A(a,bb)),bb),
      I(E(c,a),I(E(c,bb),A(M(a,bb),E(a,bb)))),
      I(I(I(c,d),a),I(I(a,c),I(bb,c)))]
    rv=I(M(a,bb),A(c,M(a,bb)))
    if mode=='split':
        k=add(c,const(2))
        seed=N(A(k,I(b.clos(const(0),const(1),k,k),N(b.req(const(1),k,k)))))
        ordinary_codes=codes+[seed]
        guarded=rv
        allcodes=codes+[rv,seed]
    elif mode=='old':
        bundle=N(I(rv,A(c,I(b.clos(a,bb,c,c),N(b.req(bb,c,c))))))
        ordinary_codes=codes
        guarded=bundle
        allcodes=codes+[bundle]
    else:raise ValueError(mode)
    imp,univ=I(a,bb),A(a,bb)
    h=add(*allcodes,a,bb,imp,univ,const(1))
    b.record(sub(var(100),h),'derived_label')
    SpF=b.product(Sp,F,'FSp');SF=b.product(S,F,'FS')
    ds=[sub(Sp,S)]
    for j,code in enumerate(ordinary_codes):
        ds.append(b.gate(add(Sp,scale(-1,S),mul(SpF,code)),'axiom_difference.'+str(j)))
    z=b.product(sub(c,a),sub(c,bb),'fresh_product')
    gr=b.gate(sub(mul(z,z),mul(add(d,const(1)),add(d,const(1)))),'fresh_guard')
    gd=b.gate(add(Sp,scale(-1,S),mul(SpF,guarded)),'guarded_difference')
    joint=b.gate(add(mul(gr,gr),mul(gd,gd)),'guarded_sum')
    ma=b.gate(add(S,mul(SF,a)),'mp.left')
    mw=b.gate(add(const(1),mul(F,imp)),'mp.weight')
    md=b.gate(add(Sp,mul(SpF,bb),scale(-1,mul(ma,mw))),'mp.difference')
    gg=b.gate(add(Sp,scale(-1,S),mul(SpF,univ),scale(-1,mul(SF,bb))),'gen.difference')
    ds.extend([md,gg])
    prod=ds[0]
    for j,z in enumerate(ds[1:]):prod=b.product(prod,z,'branch_product.'+str(j))
    sqp=b.square(prod,'branch_square')
    y=add(var(5),const(-1));C=var(17)
    den=b.gate(add(const(1),mul(add(C,const(1)),y)),'beta.denominator')
    b0=b.gate(add(S,mul(den,var(15))),'beta.first_sum')
    b1=b.gate(add(Sp,mul(add(den,y),var(16))),'beta.second_sum')
    e0=sub(var(1),b0);e1=sub(var(1),b1)
    local=add(mul(sqp,joint),mul(e0,e0),mul(e1,e1))
    b.record(sub(mul(var(18),var(101)),local),'local_congruence')
    semantic={'standard_codes':[terms(p) for p in codes], 'guarded_code':terms(guarded),
      'unguarded_codes':[terms(p) for p in ordinary_codes], 'derived_label':terms(h),
      'implication':terms(imp),'universal':terms(univ),'guard_residual':terms(gr),
      'guard_difference':terms(gd),'branch_differences':[terms(p) for p in ds],
      'local_expression':terms(local),'mode':mode}
    return b,semantic

def compact(eq):
    live=sorted({i for r in eq['residuals'] for _,m in r['terms'] for i in m})
    ren={i:j for j,i in enumerate(live)}
    new=copy.deepcopy(eq)
    new['variables']=[eq['variables'][i] for i in live]
    new['residuals']=[dict(r,terms=[[c,[ren[i] for i in m]] for c,m in r['terms']]) for r in eq['residuals']]
    return new,ren

def expand(eq):
    ans={}
    for r in eq['residuals']:
        p=poly(r['terms']);ans=add(ans,mul(p,p))
    return ans

def build(out,mode='split'):
    path=ROOT/'source/parent225/equation.json'
    raw=path.read_bytes();old=json.loads(raw)
    variables=copy.deepcopy(old['variables'])
    b,semantic=make_local(variables,mode)
    removed=set(range(5,87))|{157}
    rows=[copy.deepcopy(r) for i,r in enumerate(old['residuals']) if i not in removed]+b.rows
    eq={'schema':'conzfc-split-seed-v1','domain':'unrestricted integers',
      'polynomial':'sum(square(row) for row in residuals)','variant':mode,
      'variables':variables,'residuals':rows,'parent_equation_sha256':hashlib.sha256(raw).hexdigest()}
    final,ren=compact(eq)
    ep=expand(final)
    metrics={'variables':len(final['variables']),'rows':len(final['residuals']),
      'degree':degree(ep),'monomials':len(ep),'height':max(map(abs,ep.values())),
      'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms']),
      'new_local_gates':len(b.ledger),'new_local_rows':len(b.rows)}
    cert={'schema':'split_seed_graft_v1','mode':mode,'parent_sha256':hashlib.sha256(raw).hexdigest(),
      'removed_parent_rows':sorted(removed),'gate_ledger':b.ledger,'semantic':semantic,
      'original_to_final':[[i,j] for i,j in ren.items()]}
    out.mkdir(parents=True,exist_ok=True)
    for fn,ob in [('equation.json',final),('uncontracted.json',eq),('certificate.json',cert),('metrics.json',metrics),
      ('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':len(final['variables']),'terms':terms(ep)})]:
        (out/fn).write_bytes(canonical(ob))
    print(json.dumps(metrics))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--mode',default='split',choices=['split','old'])
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args();build(args.output,args.mode)
