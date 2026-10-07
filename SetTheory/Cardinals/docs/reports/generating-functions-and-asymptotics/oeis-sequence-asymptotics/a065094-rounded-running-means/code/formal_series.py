#!/usr/bin/env python3
"""All-order finite formal arithmetic over Q; no SymPy dependency.

Each list represents a polynomial modulo x**(order+1). Generators accept any
fixed order; costs grow with order, and convergence is neither used nor claimed.
The classical Perron theorem, not formal cancellation, supplies asymptotic validity.
"""
from fractions import Fraction as F
import argparse
import json
import sys
sys.dont_write_bytecode = True


def need(condition, message):
    if not condition:
        raise ArithmeticError(message)


class Ring:
    def __init__(self, order):
        need(type(order) is int and order >= 0, 'nonnegative integer order required')
        self.n = order

    def poly(self, values=()):
        return [F(v) for v in values[:self.n+1]] + [F(0)]*max(0, self.n+1-len(values))

    def const(self, a):
        return self.poly([a])

    def monomial(self, degree, value=1):
        need(type(degree) is int and degree >= 0, 'invalid monomial degree')
        return self.poly([0]*degree+[value])

    def add(self, *polys):
        return [sum((p[i] for p in polys), F(0)) for i in range(self.n+1)]

    def scale(self, p, a):
        return [v*a for v in p]

    def mul(self, p, q):
        return [sum((p[k]*q[i-k] for k in range(i+1)), F(0)) for i in range(self.n+1)]

    def shift(self, p, k):
        need(type(k) is int and k >= 0, 'invalid shift')
        return self.poly([0]*k+p)

    def power_unit(self, p, exponent):
        """Generalized binomial series, defined here only when p(0)=1."""
        need(p[0] == 1, 'unit power requires constant coefficient 1')
        u = self.add(p, self.const(-1))
        term, result, binomial = self.const(1), self.const(1), F(1)
        for k in range(1, self.n+1):
            term = self.mul(term, u)
            binomial *= (F(exponent)-k+1)/k
            result = self.add(result, self.scale(term, binomial))
        return result

    def exp(self, p):
        need(p[0] == 0, 'rational formal exponential requires constant 0')
        result = self.const(1)
        for n in range(1, self.n+1):
            result[n] = sum((k*p[k]*result[n-k] for k in range(1,n+1)), F(0))/n
        return result

    def log(self, p):
        need(p[0] == 1, 'formal logarithm requires constant 1')
        inv = self.power_unit(p, -1)
        return [F(0)]+[sum((k*p[k]*inv[n-k] for k in range(1,n+1)), F(0))/n
                         for n in range(1,self.n+1)]


def recurrence_basis(j, order):
    r = Ring(order)
    shifts=[]
    for sign in (1,-1):
        # One extra power is necessary before division by h.
        rr=Ring(order+1)
        root=rr.power_unit(rr.add(rr.const(1),rr.monomial(2,sign)),F(1,2))
        exponent=r.poly([2*x for x in root[1:]])
        factor=r.power_unit(r.add(r.const(1),r.monomial(2,sign)), -F(1,4)-F(j,2))
        shifts.append(r.shift(r.mul(r.exp(exponent),factor),j))
    return r.add(shifts[0],r.monomial(j,-2),shifts[1],r.shift(r.scale(shifts[1],-1),2))


def forward_coefficients(order):
    need(type(order) is int and order>=0, 'invalid forward order')
    r=Ring(order+3)
    basis=[recurrence_basis(j,r.n) for j in range(order+1)]
    c=[F(1)]
    residue=basis[0]
    need(all(x == 0 for x in residue[:4]), 'leading recurrence balance failed')
    for j in range(1,order+1):
        need(all(x == 0 for x in basis[j][:j+3]) and basis[j][j+3] == -j,
             'triangular recurrence pivot failed')
        c.append(residue[j+3]/j)
        residue=r.add(residue,r.scale(basis[j],c[j]))
        need(all(x == 0 for x in residue[:j+4]), 'forward recurrence cancellation failed')
    return c


def log_coefficients(c, order):
    need(len(c)>order and c[0]==1, 'insufficient normalized forward coefficients')
    return Ring(order).log([F(v)*2**j for j,v in enumerate(c[:order+1])])


def inverse_residual(delta,b,order):
    r=Ring(order)
    unit=r.add(r.const(1),r.shift(r.poly(delta),1))
    terms=[r.poly(delta),r.scale(r.log(unit),-F(1,2))]
    for j in range(1,min(order,len(b)-1)+1):
        terms.append(r.shift(r.scale(r.power_unit(unit,-j),b[j]),j))
    return r.add(*terms)


def inverse_coefficients(b,order):
    need(type(order) is int and order>=1 and len(b)>order and b[0]==0,
         'invalid inverse order or logarithmic data')
    r=Ring(order)
    delta=r.const(0)
    for j in range(1,order+1):
        residue=inverse_residual(delta,b,order)
        delta[j]=-residue[j]
        need(all(x==0 for x in inverse_residual(delta,b,order)[:j+1]),
             'inverse coefficient cancellation failed')
    # n-t0^2/4 = delta/(2v) + delta^2/4. Output through v**(order-1).
    correction=r.add(r.poly([x/2 for x in delta[1:]]),r.scale(r.mul(delta,delta),F(1,4)))
    return delta,correction[:order]


def check_by_log_ratios(c):
    """Distinct recurrence route: exponentiate logarithmic forward/back ratios."""
    order=len(c)+2
    r=Ring(order)
    logc=Ring(len(c)-1).log(c)
    ratios=[]
    for sign in (1,-1):
        unit=r.add(r.const(1),r.monomial(2,sign))
        rr=Ring(order+1)
        root=rr.power_unit(rr.add(rr.const(1),rr.monomial(2,sign)),F(1,2))
        terms=[r.poly([2*x for x in root[1:]]),r.scale(r.log(unit),-F(1,4))]
        for j in range(1,len(c)):
            terms.append(r.shift(r.scale(r.add(r.power_unit(unit,-F(j,2)),r.const(-1)),logc[j]),j))
        ratios.append(r.exp(r.add(*terms)))
    residual=r.add(ratios[0],ratios[1],r.shift(r.scale(ratios[1],-1),2),r.const(-2))
    need(all(x==0 for x in residual),'log-ratio recurrence check failed')
    return order


def check_inverse_composition(c,correction):
    """Compose the n(t0) inverse directly into the original logarithmic carrier."""
    order=len(correction)
    r=Ring(order+1)
    unit=r.add(r.const(1),r.shift(r.scale(r.poly(correction),4),2))
    root=r.power_unit(unit,F(1,2))
    target=Ring(order)
    residual=target.add(target.poly(root[1:]),target.scale(target.poly(r.log(unit)),-F(1,4)))
    logc=target.log(target.poly(c))
    for j in range(1,order+1):
        term=r.shift(r.scale(r.power_unit(unit,-F(j,2)),logc[j]*2**j),j)
        residual=target.add(residual,target.poly(term))
    need(all(x==0 for x in residual),'direct inverse composition failed')
    return order


PUBLISHED_C=list(map(F,['1','-17/48','649/4608','-56533/3317760','7946069/637009920','937900373/42807066624','2719850722091/308210879692800']))
PUBLISHED_B=list(map(F,['0','-17/24','5/16','277/1920','21/128','85009/107520']))
PUBLISHED_DELTA=list(map(F,['0','17/24','1/24','-3601/5760','-17/90','223543/967680']))
PUBLISHED_INVERSE=list(map(F,['17/48','1/48','-539/2880','-51/640','-25517/241920']))


def generate(order=9):
    need(type(order) is int and order>=6, 'at least six forward corrections required for displayed checks')
    c=forward_coefficients(order)
    b=log_coefficients(c,order)
    delta,correction=inverse_coefficients(b,order)
    need(c[:7]==PUBLISHED_C,'published forward coefficients differ')
    need(b[:6]==PUBLISHED_B,'published logarithmic coefficients differ')
    need(delta[:6]==PUBLISHED_DELTA,'published delta coefficients differ')
    need(correction[:5]==PUBLISHED_INVERSE,'published range inverse differs')
    degree=check_by_log_ratios(c)
    inverse_degree=check_inverse_composition(c,correction)
    return {'status':'PASS','arithmetic':'fractions.Fraction, standard library only',
            'all_order_algorithm':True,'forward_order':order,
            'c':[str(x) for x in c], 'b':[str(x) for x in b],
            'delta':[str(x) for x in delta],
            'n_minus_t0_squared_over_4':[str(x) for x in correction],
            'independent_log_ratio_cancellation_through_h_power':degree,
            'direct_inverse_composition_through_t0_inverse_power':inverse_degree,
            'asymptotic_validity_requires_classical_Perron_theorem':True}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order',type=int,default=9)
    print(json.dumps(generate(parser.parse_args().order),indent=2,sort_keys=True))
