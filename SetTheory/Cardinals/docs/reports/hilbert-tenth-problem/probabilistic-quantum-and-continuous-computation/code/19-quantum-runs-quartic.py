"""Canonical natural-number quartic certificates for rational circuits.

A polynomial is exported as a sum of squares of sparse quadratic residuals.
The format is exact and avoids expanding a potentially large quartic.
Every rational wire and every gate auxiliary has a unique natural encoding.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import json
from typing import Any


class Poly:
    def __init__(self, terms=None):
        if isinstance(terms, int):
            terms = {(): terms} if terms else {}
        self.terms = {tuple(k): int(v) for k,v in (terms or {}).items() if v}

    @staticmethod
    def var(i):
        return Poly({(i,): 1})

    def __add__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        d = self.terms.copy()
        for k,v in other.terms.items():
            d[k] = d.get(k,0)+v
        return Poly(d)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k:-v for k,v in self.terms.items()})

    def __sub__(self, other):
        return self + -(other if isinstance(other,Poly) else Poly(other))

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        other = other if isinstance(other, Poly) else Poly(other)
        d = {}
        for a,v in self.terms.items():
            for b,w in other.terms.items():
                k=tuple(sorted(a+b)); d[k]=d.get(k,0)+v*w
        return Poly(d)

    __rmul__=__mul__

    def evaluate(self, assignment):
        total=0
        for ids,c in self.terms.items():
            term=c
            for i in ids:
                term*=assignment[i]
            total+=term
        return total

    def serialized(self):
        return [[c,list(ids)] for ids,c in sorted(self.terms.items())]


@dataclass
class Wire:
    name: str
    value: Fraction
    indices: list[int]

    @property
    def n(self):
        return Poly.var(self.indices[0])-Poly.var(self.indices[1])

    @property
    def d(self):
        return Poly.var(self.indices[2])+1


class Circuit:
    def __init__(self):
        self.names=[]; self.values=[]; self.residuals=[]; self.wires=[]
        self.additions=0; self.multiplications=0; self.equalities=0

    def natural(self, name, value):
        value=int(value)
        if value < 0:
            raise ValueError("A natural witness cannot be negative")
        i=len(self.names); self.names.append(name); self.values.append(value)
        return Poly.var(i), i

    def residual(self, p):
        if any(len(k)>2 for k in p.terms):
            raise ValueError("A residual is not quadratic")
        self.residuals.append(p)

    def rational(self, name, value, pin=False):
        q=Fraction(value); n=q.numerator; d=q.denominator
        u=0 if d==1 else pow(n,-1,d)
        v=(n*u-1)//d
        vals=[max(n,0),max(-n,0),d-1,u,max(v,0),max(-v,0),d-1-u]
        indices=[]
        for suffix,val in zip(('p','m','h','u','vp','vm','s'), vals):
            _,i=self.natural(name+'.'+suffix,val); indices.append(i)
        w=Wire(name,q,indices); self.wires.append(w)
        p,m,h,u,vp,vm,s=(Poly.var(i) for i in indices)
        self.residual(p*m); self.residual(vp*vm)
        self.residual((p-m)*u-(h+1)*(vp-vm)-1)
        self.residual(u+s-h)
        if pin:
            self.pin(w,q)
        return w

    def pin(self,w,value):
        q=Fraction(value)
        self.residual(q.denominator*w.n-q.numerator*w.d)
        self.equalities+=1

    def equal(self,a,b):
        self.residual(a.n*b.d-b.n*a.d); self.equalities+=1

    def signed_aux(self,name,value,expr):
        p,_=self.natural(name+'.plus',max(value,0))
        m,_=self.natural(name+'.minus',max(-value,0))
        self.residual(p*m); self.residual(p-m-expr)
        return p-m

    def add(self,a,b,subtract=False):
        tag='sub' if subtract else 'add'; name=f'{tag}{self.additions}'
        self.additions+=1
        c=self.rational(name,a.value-b.value if subtract else a.value+b.value)
        r=self.signed_aux(name+'.r',a.value.numerator*b.value.denominator,a.n*b.d)
        t=self.signed_aux(name+'.t',b.value.numerator*a.value.denominator,b.n*a.d)
        k,_=self.natural(name+'.k',a.value.denominator*b.value.denominator)
        self.residual(k-a.d*b.d)
        self.residual((r-t if subtract else r+t)*c.d-c.n*k)
        return c

    def mul(self,a,b):
        name=f'mul{self.multiplications}'; self.multiplications+=1
        c=self.rational(name,a.value*b.value)
        r=self.signed_aux(name+'.r',a.value.numerator*b.value.numerator,a.n*b.n)
        k,_=self.natural(name+'.k',a.value.denominator*b.value.denominator)
        self.residual(k-a.d*b.d); self.residual(r*c.d-c.n*k)
        return c

    def matrix(self,name,m,pin=False):
        return [[self.rational(f'{name}[{i},{j}]',Fraction(m[i,j]),pin)
                 for j in range(m.cols)] for i in range(m.rows)]

    def matmul(self,a,b):
        if not a or not b or len(a[0])!=len(b):
            raise ValueError('Bad matrix product dimensions')
        out=[]
        for row in a:
            result=[]
            for j in range(len(b[0])):
                terms=[self.mul(row[k],b[k][j]) for k in range(len(b))]
                s=terms[0]
                for t in terms[1:]:
                    s=self.add(s,t)
                result.append(s)
            out.append(result)
        return out

    def stats(self):
        W=len(self.wires); a=self.additions; m=self.multiplications; e=self.equalities
        result=dict(rational_wires=W,additions=a,multiplications=m,equalities=e,
                    natural_variables=len(self.names),quadratic_residuals=len(self.residuals))
        assert len(self.names)==7*W+5*a+3*m
        assert len(self.residuals)==4*W+6*a+4*m+e
        return result

    def export(self,path,metadata):
        failures=[i for i,p in enumerate(self.residuals) if p.evaluate(self.values)!=0]
        if failures:
            raise ArithmeticError(f'Nonzero generated residuals: {failures[:5]}')
        data=dict(format='canonical-quartic-v1',polynomial='sum(residual_i**2)',
                  variable_domain='natural_numbers_including_zero',
                  variables=self.names,witness=self.values,
                  residuals=[r.serialized() for r in self.residuals],
                  rational_wires={w.name:w.indices for w in self.wires},
                  statistics=self.stats(),metadata=metadata)
        Path(path).write_text(json.dumps(data,separators=(',',':'))+'\n')
        return data


def names(matrix):
    return [[w.name for w in row] for row in matrix]


def group_core(t,g,p):
    """Dense deliberately unoptimized syntax; the paper gives its exact counts."""
    c=Circuit(); d=t.rows
    z=c.rational('zero',0,True); one=c.rational('one',1,True)
    tw=c.matrix('T',t,True); gw=c.matrix('G',g); pw=c.matrix('P',p)
    aw=[[c.add(one if i==j else z,tw[i][j],True) for j in range(d)] for i in range(d)]
    ag=c.matmul(aw,gw); ga=c.matmul(gw,aw); ap=c.matmul(aw,pw); gp=c.matmul(gw,pw)
    for i in range(d):
        for j in range(d):
            identity=one if i==j else z
            c.equal(c.add(ag[i][j],pw[i][j]),identity)
            c.equal(c.add(ga[i][j],pw[i][j]),identity)
            c.equal(ap[i][j],z); c.equal(gp[i][j],z)
    assert c.stats()['natural_variables']==88*d**3+9*d**2+14
    assert c.stats()['quadratic_residuals']==72*d**3+7*d**2+10
    metadata=dict(dimension=d,T=names(tw),G=names(gw),P=names(pw),core_statistics=c.stats())
    return c,tw,gw,pw,metadata


def full_certificate(example,order,path):
    from quantum_loops import group_inverse,normalized_factorial_moments
    t=example['T']; g,p=group_inverse(t)
    c,tw,gw,pw,meta=group_core(t,g,p)
    x=c.matrix('x',example['x'],True)
    exits=c.matrix('exits',example['exits'],True)
    ell=c.matrix('ell',example['ell'],True)
    v=c.matmul(gw,x); out=[]
    exact=normalized_factorial_moments(t,example['x'],example['exits'],order)
    for k in range(order+1):
        b=c.matmul(exits,v)
        for j in range(len(b)):
            c.pin(b[j][0],Fraction(exact[j,k]))
        out.append(names(b))
        if k!=order:
            v=c.matmul(gw,c.matmul(tw,v))
    w=c.matmul(ell,c.matmul(pw,x))
    c.pin(w[0][0],Fraction((example['ell']*p*example['x'])[0]))
    meta.update(x=names(x),exits=names(exits),ell=names(ell),moments=out,
                nontermination=names(w),moment_order=order,
                scope='Physical validity is a promise; exact algebra is certified.')
    return c.export(path,meta)


def all_moments_certificate(example,path):
    """Certify a finite recurrence determining *every* factorial moment.

    Uses a division-free-in-the-data Faddeev--LeVerrier circuit: the only
    reciprocals are fixed constants -1/k, for 1 <= k <= D.
    """
    from quantum_loops import group_inverse
    t=example['T']; D=t.rows; g,p=group_inverse(t)
    c,tw,gw,pw,meta=group_core(t,g,p)
    x=c.matrix('x',example['x'],True); exits=c.matrix('exits',example['exits'],True)
    ell=c.matrix('ell',example['ell'],True)
    zero=next(w for w in c.wires if w.name=='zero')
    one=next(w for w in c.wires if w.name=='one')
    hw=c.matmul(tw,gw)
    B=[[one if i==j else zero for j in range(D)] for i in range(D)]
    coefficients=[one]
    for k in range(1,D+1):
        product=c.matmul(hw,B)
        trace=product[0][0]
        for i in range(1,D):
            trace=c.add(trace,product[i][i])
        scale=c.rational(f'negative_reciprocal_{k}',Fraction(-1,k),True)
        ck=c.mul(scale,trace); c.pin(ck,ck.value); coefficients.append(ck)
        B=[[c.add(product[i][j],ck) if i==j else product[i][j]
            for j in range(D)] for i in range(D)]
    for row in B:
        for w in row:
            c.equal(w,zero)
    v=c.matmul(gw,x); outputs=[]
    for k in range(D):
        b=c.matmul(exits,v)
        for row in b:
            c.pin(row[0],row[0].value)
        outputs.append(names(b))
        if k+1<D:
            v=c.matmul(hw,v)
    w=c.matmul(ell,c.matmul(pw,x)); c.pin(w[0][0],w[0][0].value)
    meta.update(x=names(x),exits=names(exits),ell=names(ell),moments=outputs,
                nontermination=names(w),moment_order=D-1,
                all_moments_recurrence=[coef.name for coef in coefficients],
                scope='All moments via Cayley-Hamilton; physical validity is a promise.')
    return c.export(path,meta)
