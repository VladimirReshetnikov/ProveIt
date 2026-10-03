#!/usr/bin/env python3
"""Emit quadratic arithmetic equations plus fixed-base power graph atoms.

Every variable ranges over N. Signed integers use disjoint positive/negative
parts. All Boolean comparisons have uniquely forced witnesses. The compiler
is parametric in coefficients and (in finite mode) the horizon: the supplied
values only produce a sample satisfying assignment, not specialisation.
"""
from __future__ import annotations
from dataclasses import dataclass
from math import comb
import json
from pathlib import Path
from typing import Optional
from profiles import ExpPoly, Run, annihilator, make_chain, build_profiles


class Poly:
    def __init__(self, terms=None):
        if isinstance(terms,int):
            self.t = {():terms} if terms else {}
        else:
            self.t = {m:c for m,c in (terms or {}).items() if c}
    @staticmethod
    def var(i):
        return Poly({(i,):1})
    def __add__(self,o):
        o=aspoly(o); d=dict(self.t)
        for m,c in o.t.items(): d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,o): return self+-aspoly(o)
    def __rsub__(self,o): return aspoly(o)+-self
    def __mul__(self,o):
        o=aspoly(o); d={}
        for m,c in self.t.items():
            for n,e in o.t.items():
                k=tuple(sorted(m+n)); d[k]=d.get(k,0)+c*e
        return Poly(d)
    __rmul__=__mul__
    def value(self,v):
        out=0
        for m,c in self.t.items():
            for i in m: c*=v[i]
            out+=c
        return out
    def degree(self): return max(map(len,self.t),default=0)
    def key(self): return tuple(sorted(self.t.items()))
    def data(self): return [[c,list(m)] for m,c in sorted(self.t.items())]


def aspoly(x): return x if isinstance(x,Poly) else Poly(x)


class Circuit:
    def __init__(self):
        self.names=[]; self.values=[]; self.roles=[]
        self.residuals=[]; self.power_atoms=[]
        self.sign_cache={}
    def var(self,name,value,role='witness'):
        if not isinstance(value,int) or value<0: raise ValueError((name,value))
        i=len(self.values); self.names.append(name); self.values.append(value); self.roles.append(role)
        return Poly.var(i)
    def eq(self,p):
        p=aspoly(p)
        if p.degree()>2: raise AssertionError('Non-quadratic residual')
        if p.t: self.residuals.append(p)
    def nat(self,p,name='computed'):
        p=aspoly(p); v=self.var(name,p.value(self.values)); self.eq(v-p); return v
    def integer(self,p,name='signed'):
        p=aspoly(p); x=p.value(self.values)
        a=self.var(name+'+',max(x,0)); b=self.var(name+'-',max(-x,0))
        self.eq(a-b-p); self.eq(a*b)
        return a,b
    def zero(self,n):
        n=aspoly(n); x=n.value(self.values)
        if x<0: raise AssertionError('Natural zero test applied to negative expression')
        z=self.var('zero?',int(x==0)); k=self.var('zero-test slack',max(x-1,0))
        self.eq(z*(z-1)); self.eq(z*n)
        self.eq((1-z)*(n-1-k)); self.eq(z*k)
        return z
    def signs(self,p):
        p=aspoly(p); key=p.key()
        if key in self.sign_cache: return self.sign_cache[key]
        a,b=self.integer(p,'sign value')
        za,zb=self.zero(a),self.zero(b)
        ans=(1-zb,self.band(za,zb),1-za)  # negative, zero, positive
        self.sign_cache[key]=ans
        return ans
    def band(self,*xs):
        out=aspoly(1)
        for x in xs: out=self.nat(out*aspoly(x),'and')
        return out
    def bor(self,x,y): return self.nat(x+y-x*y,'or')
    def le(self,x,y):
        p,_=self.integer(aspoly(x)-aspoly(y),'comparison difference')
        return self.zero(p)
    def implies(self,g,p): self.eq(aspoly(g)*aspoly(p))
    def match(self,g,left,right):
        for x,y in zip(left,right): self.implies(g,x-y)
    def power(self,b,n):
        n=aspoly(n)
        if b==1: return aspoly(1)
        k=n.key()
        if len(k)==1 and len(k[0][0])==1 and k[0][1]==1:
            ni=k[0][0][0]
        else:
            nn=self.nat(n,'power exponent'); ni=next(iter(nn.t))[0]
        p=self.var(f'power {b}',pow(b,self.values[ni]))
        pi=next(iter(p.t))[0]
        self.power_atoms.append({'base':b,'exponent':ni,'result':pi})
        return p
    def valid(self,values=None):
        v=self.values if values is None else values
        if len(v)!=len(self.values) or any(not isinstance(x,int) or x<0 for x in v): return False
        if any(p.value(v)!=0 for p in self.residuals): return False
        return all(v[a['result']]==pow(a['base'],v[a['exponent']]) for a in self.power_atoms)
    def metadata(self):
        return {'variables':len(self.values),'inputs':self.roles.count('input'),
                'witnesses':self.roles.count('witness'),'quadratic_residuals':len(self.residuals),
                'power_atoms':len(self.power_atoms),
                'max_residual_degree':max((p.degree() for p in self.residuals),default=0),
                'max_witness_bits':max((x.bit_length() for x,r in zip(self.values,self.roles) if r=='witness'),default=0)}
    def export(self,path:Path,expand=False):
        data={'format':'canonical-positive-spectrum-v1','domain':'nonnegative integers',
              'semantics':'sum(residual**2)=0 AND every listed power atom',
              'metadata':self.metadata(),'variables':[{'index':i,'name':n,'role':r} for i,(n,r) in enumerate(zip(self.names,self.roles))],
              'quadratic_residuals':[p.data() for p in self.residuals],
              'power_atoms':self.power_atoms,'sample_assignment':self.values}
        if expand:
            q=aspoly(0)
            for p in self.residuals: q=q+p*p
            data['expanded_quartic']=q.data()
            data['metadata']['expanded_quartic_monomials']=len(q.t)
            data['metadata']['expanded_quartic_degree']=q.degree()
        path.write_text(json.dumps(data,separators=(',',':'))+'\n')
        return data['metadata']


def symbolic_chain(c:Circuit,terms:dict[int,list[int]],shape:dict[int,int]):
    f={}
    for b,d in sorted(shape.items()):
        f[b]=[]
        for k in range(d+1):
            val=terms.get(b,[])[k] if k<len(terms.get(b,[])) else 0
            p=c.var(f'coefficient {b}:{k} +',max(val,0),'input')
            n=c.var(f'coefficient {b}:{k} -',max(-val,0),'input')
            c.eq(p*n); f[b].append(p-n)
    fs=[f]
    for a in annihilator(shape):
        new={}
        for b,cs in f.items():
            arr=[b*sum((comb(h,k)*cs[h] for h in range(k,len(cs))),aspoly(0))-a*cs[k]
                 for k in range(len(cs))]
            while arr and not arr[-1].t: arr.pop()
            if arr: new[b]=arr
        f=new; fs.append(f)
    assert not fs[-1]
    # Share transformed coefficients across all endpoint evaluations.
    for j in range(1,len(fs)-1):
        for b,cs in fs[j].items():
            for k,co in enumerate(cs):
                p,n=c.integer(co,'transformed coefficient')
                cs[k]=p-n
    return fs


def eventual(c:Circuit,f):
    pref=aspoly(1); minus=aspoly(0); plus=aspoly(0)
    for b in sorted(f,reverse=True):
        for co in reversed(f[b]):
            m,z,p=c.signs(co)
            minus=minus+c.band(pref,m); plus=plus+c.band(pref,p)
            pref=c.band(pref,z)
    return minus,pref,plus


def evaluate(c:Circuit,f,n):
    parts=[]
    for b,cs in sorted(f.items()):
        cur=aspoly(0)
        for co in reversed(cs):
            p,q=c.integer(cur*n+co,'Horner')
            cur=p-q
        power=c.power(b,n)
        p,q=c.integer(cur*power,'exponential term')
        parts.append(p-q)
    p,q=c.integer(sum(parts,aspoly(0)),'evaluation')
    return p-q


@dataclass
class Row:
    a:Poly
    lo:Poly
    hi:Poly
    signs:tuple[Poly,Poly,Poly]
    finite:Poly|None=None
    tail:Poly|None=None


def compile_certificate(terms:dict[int,list[int]],shape:dict[int,int],horizon:Optional[int],
                        profiles:Optional[list[list[Run]]]=None):
    f=ExpPoly(terms); concrete,_=make_chain(f,shape)
    if profiles is None: profiles=build_profiles(concrete,horizon)
    c=Circuit(); fs=symbolic_chain(c,terms,shape)
    T=None if horizon is None else c.var('horizon',horizon,'input')
    D=len(fs)-1
    allrows=[]
    for j in range(D+1):
        cap=1 if j==D else 2*(D-j)-1
        if len(profiles[j])>cap: raise ValueError('Profile exceeds capacity')
        rows=[]
        for k in range(cap):
            r=profiles[j][k] if k<len(profiles[j]) else None
            a=c.var(f'level {j} row {k} active',int(r is not None))
            lo=c.var(f'level {j} row {k} left',r.lo if r else 0)
            hi=c.var(f'level {j} row {k} right',r.hi if r and r.hi is not None else 0)
            s=tuple(c.var(f'level {j} row {k} sign {v}',int(r is not None and r.sign==v)) for v in (-1,0,1))
            rows.append(Row(a,lo,hi,s))
            c.eq(a*(a-1)); c.eq(sum(s,aspoly(0))-a)
            c.eq((1-a)*lo); c.eq((1-a)*hi)
        for k,r in enumerate(rows):
            nxt=rows[k+1].a if k+1<len(rows) else aspoly(0)
            if k==0: c.eq(r.a-1); c.eq(r.lo)
            else:
                p=rows[k-1]
                c.eq(r.a*(1-p.a)); c.implies(r.a,r.lo-p.hi-1)
                c.eq(sum((x*y for x,y in zip(p.signs,r.signs)),aspoly(0)))
            if T is not None:
                r.finite=r.a; r.tail=aspoly(0)
                c.implies(r.a,1-c.le(r.lo,r.hi)); c.implies(r.a,1-c.le(r.hi,T))
                c.implies(r.a-nxt,r.hi-T)
            else:
                r.finite=nxt; r.tail=r.a-nxt
                c.eq((1-nxt)*r.hi)
                c.implies(nxt,1-c.le(r.lo,r.hi))
        allrows.append(rows)
    # f_D is identically zero: pin its unique descriptor.
    bottom=allrows[-1][0]
    c.eq(bottom.signs[0]); c.eq(bottom.signs[1]-1); c.eq(bottom.signs[2])
    for j in reversed(range(D)):
        rows,children=allrows[j],allrows[j+1]
        ev=eventual(c,fs[j]) if T is None else None
        def val_sign(n): return c.signs(evaluate(c,fs[j],n))
        for r in rows:
            c.match(r.a,val_sign(r.lo),r.signs)
            c.match(r.finite,val_sign(r.hi),r.signs)
            if ev is not None: c.match(r.tail,ev,r.signs)
        for ch in children:
            endpoints=[(ch.lo,ch.a)]
            if T is None:
                endpoints.append((ch.hi+1,ch.finite))
            else:
                raw=ch.hi+1; le=c.le(raw,T)
                u=c.nat(le*(raw-T)+T,'clipped lifted endpoint')
                endpoints.append((u,ch.a))
            for x,enabled in endpoints:
                sx=val_sign(x)
                for r in rows:
                    lower=c.le(r.lo,x); upper=c.le(x,r.hi)
                    if T is None: upper=c.bor(r.tail,upper)
                    gate=c.band(r.a,enabled,lower,upper)
                    c.match(gate,sx,r.signs)
    return c,profiles


def main():
    out=Path(__file__).resolve().parent.parent/'data'
    out.mkdir(exist_ok=True)
    terms={1:[64],2:[-20],4:[1]}; shape={1:0,2:0,4:0}
    summary={}
    for name,T in [('finite',6),('infinite',None)]:
        c,p=compile_certificate(terms,shape,T)
        assert c.valid()
        summary[name]=c.export(out/f'{name}_certificate.json',expand=True)
    (out/'compiler_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__': main()
