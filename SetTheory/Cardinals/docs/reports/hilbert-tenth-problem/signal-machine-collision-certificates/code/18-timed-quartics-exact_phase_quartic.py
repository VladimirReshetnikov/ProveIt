#!/usr/bin/env python3
"""Exact, immutable finite-chart -> quartic compiler used by the accompanying audit.

The caller must prove its chart output map is globally injective. This module
checks syntax, exactness, dimensions and degrees, not that semantic hypothesis.
All witnesses are literal Python ints >= 0 (bool and float are rejected).
"""
from dataclasses import dataclass
from fractions import Fraction
from math import lcm
from typing import Iterable


def integer(x, name="integer", nonnegative=False):
    if type(x) is not int or (nonnegative and x < 0):
        raise TypeError(f"{name} must be a strict {'natural' if nonnegative else 'integer'}")
    return x


def rational(x):
    if type(x) is int:
        return Fraction(x)
    if type(x) is Fraction:
        return x
    raise TypeError("coefficients must be exact int or Fraction, never bool/float")


@dataclass(frozen=True)
class Poly:
    arity: int
    terms: tuple

    def __post_init__(self):
        integer(self.arity, "arity", True)
        combined = {}
        # Snapshot both layers; do not retain caller-owned nested containers.
        for raw in self.terms:
            if len(raw) != 2:
                raise ValueError("each term is (exponents, coefficient)")
            powers, coefficient = tuple(raw[0]), rational(raw[1])
            if len(powers) != self.arity:
                raise ValueError("wrong monomial arity")
            for p in powers:
                integer(p, "exponent", True)
            combined[powers] = combined.get(powers, Fraction(0)) + coefficient
        object.__setattr__(self, "terms", tuple(sorted((p,c) for p,c in combined.items() if c)))

    @property
    def degree(self):
        return max((sum(p) for p,c in self.terms), default=0)

    @classmethod
    def const(cls, arity, c):
        return cls(arity, (((0,)*arity, rational(c)),))

    @classmethod
    def var(cls, arity, index):
        integer(index, "variable index", True)
        if index >= arity:
            raise ValueError("variable index out of range")
        p = [0]*arity
        p[index] = 1
        return cls(arity, ((p, 1),))

    def _coerce(self, other):
        if isinstance(other, Poly):
            if self.arity != other.arity:
                raise ValueError("polynomial arity mismatch")
            return other
        return Poly.const(self.arity, other)

    def __add__(self, other):
        other = self._coerce(other)
        return Poly(self.arity, self.terms + other.terms)
    __radd__ = __add__

    def __neg__(self):
        return Poly(self.arity, tuple((p,-c) for p,c in self.terms))

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) + (-self)

    def __mul__(self, other):
        other = self._coerce(other)
        return Poly(self.arity, tuple((tuple(a+b for a,b in zip(p,q)), c*d)
                    for p,c in self.terms for q,d in other.terms))
    __rmul__ = __mul__

    def __pow__(self, power):
        integer(power, "power", True)
        result = Poly.const(self.arity, 1)
        for _ in range(power):
            result = result*self
        return result

    def __call__(self, values):
        values = tuple(values)
        if len(values) != self.arity:
            raise ValueError("wrong evaluation arity")
        for x in values:
            integer(x, "polynomial evaluation coordinate")
        result = Fraction(0)
        for powers, coefficient in self.terms:
            term = coefficient
            for x,p in zip(values,powers):
                term *= x**p
            result += term
        return result

    def clear_denominators(self):
        denominator = lcm(*(c.denominator for p,c in self.terms))
        return denominator, denominator*self

    def homogenized_lift(self, arity, parameter_indices, selector_index):
        """Only constant terms become c*selector. All positive degrees stay put."""
        if len(parameter_indices) != self.arity:
            raise ValueError("wrong lift parameter count")
        lifted = []
        for powers,c in self.terms:
            target = [0]*arity
            if not any(powers):
                target[selector_index] = 1
            else:
                for index,power in zip(parameter_indices,powers):
                    target[index] += power
            lifted.append((target,c))
        return Poly(arity, lifted)


@dataclass(frozen=True)
class Chart:
    name: str
    parameters: int
    outputs: tuple
    inequalities: tuple = ()
    equalities: tuple = ()

    def __post_init__(self):
        integer(self.parameters, "parameter count", True)
        if type(self.name) is not str or not self.name:
            raise TypeError("chart name must be a nonempty string")
        for field, degree in (("outputs",2),("inequalities",1),("equalities",1)):
            polys = tuple(getattr(self,field))
            for p in polys:
                if type(p) is not Poly or p.arity != self.parameters or p.degree > degree:
                    raise ValueError(f"malformed {field} polynomial")
            object.__setattr__(self,field,polys)


@dataclass(frozen=True)
class Certificate:
    charts: tuple
    external_count: int
    witness_names: tuple
    layouts: tuple
    residuals: tuple
    nonnegative_products: tuple
    expression: Poly
    mode: str
    natural_external_indices: tuple = ()

    def __post_init__(self):
        integer(self.external_count, "external count", True)
        for field in ("charts","witness_names","layouts","residuals","nonnegative_products","natural_external_indices"):
            value = tuple(getattr(self,field))
            if field == "layouts":
                value = tuple((tuple(z),tuple(u)) for z,u in value)
            object.__setattr__(self,field,value)
        if any(type(c) is not Chart for c in self.charts):
            raise TypeError("certificate charts must be Chart objects")
        if any(type(name) is not str for name in self.witness_names):
            raise TypeError("witness names must be strings")
        if len(set(self.witness_names)) != len(self.witness_names):
            raise ValueError("duplicate witness names")
        if self.mode not in ("sos","products"):
            raise ValueError("invalid certificate mode")
        arity = self.external_count+len(self.witness_names)
        for index in self.natural_external_indices:
            integer(index,"natural external index",True)
            if index >= self.external_count:
                raise ValueError("natural external index out of range")
        for z,u in self.layouts:
            for index in z+u:
                integer(index,"layout index",True)
                if index < self.external_count or index >= arity:
                    raise ValueError("layout index out of range")
        for p in self.residuals+self.nonnegative_products+(self.expression,):
            if type(p) is not Poly or p.arity != arity:
                raise ValueError("malformed certificate polynomial")
            if any(c.denominator != 1 for powers,c in p.terms):
                raise ValueError("certificate coefficients must be integral")
        rebuilt = sum((r*r for r in self.residuals),Poly.const(arity,0)) + sum(self.nonnegative_products,Poly.const(arity,0))
        if self.expression != rebuilt or self.expression.degree > 4:
            raise ValueError("certificate expression does not match its quartic residuals")

    def evaluate(self, external, witness):
        external, witness = tuple(external), tuple(witness)
        if len(external) != self.external_count or len(witness) != len(self.witness_names):
            raise ValueError("wrong external or witness arity")
        for x in external:
            integer(x, "external coordinate")
        for index in self.natural_external_indices:
            integer(external[index], "natural external coordinate", True)
        for x in witness:
            integer(x, "witness coordinate", True)
        answer = self.expression(external+witness)
        assert answer.denominator == 1
        return answer.numerator

    def witness(self, chart_index, parameters):
        integer(chart_index, "chart index", True)
        if chart_index >= len(self.charts):
            raise ValueError("chart index out of range")
        parameters = tuple(parameters)
        chart = self.charts[chart_index]
        if len(parameters) != chart.parameters:
            raise ValueError("wrong chart parameter count")
        for z in parameters:
            integer(z, "chart parameter", True)
        result = [0]*len(self.witness_names)
        result[chart_index] = 1
        zs,us = self.layouts[chart_index]
        for index,value in zip(zs,parameters):
            result[index-self.external_count] = value
        for index,a in zip(us,chart.inequalities):
            _,a = a.clear_denominators()
            value = a(parameters)
            if value < 0:
                raise ValueError("parameters violate chart inequality")
            assert value.denominator == 1
            result[index-self.external_count] = value.numerator
        if any(a(parameters) != 0 for a in chart.equalities):
            raise ValueError("parameters violate chart equality")
        return tuple(result)


def compile_charts(charts: Iterable[Chart], mode="sos", external_count=None):
    charts = tuple(charts)
    if any(type(c) is not Chart for c in charts):
        raise TypeError("compiler expects Chart objects")
    if mode not in ("sos","products"):
        raise ValueError("mode must be sos or products")
    if not charts:
        if external_count is None:
            raise ValueError("empty family needs explicit external_count")
        q = integer(external_count,"external count",True)
        return Certificate((),q,(),(),(Poly.const(q,1),),(),Poly.const(q,1),mode)
    q = len(charts[0].outputs)
    if external_count is not None and integer(external_count,"external count",True) != q:
        raise ValueError("external count mismatch")
    if any(len(c.outputs) != q for c in charts):
        raise ValueError("inconsistent output dimensions")
    b = len(charts)
    names = [f"e{i}" for i in range(b)]
    layouts = []
    for i,c in enumerate(charts):
        z = tuple(q+len(names)+j for j in range(c.parameters))
        names.extend(f"z{i}_{j}" for j in range(c.parameters))
        u = tuple(q+len(names)+j for j in range(len(c.inequalities)))
        names.extend(f"u{i}_{j}" for j in range(len(c.inequalities)))
        layouts.append((z,u))
    arity = q+len(names)
    variables = tuple(Poly.var(arity,j) for j in range(arity))
    e = variables[q:q+b]
    E = sum(e,Poly.const(arity,0))
    residuals, products = [E-1], []
    for i,c in enumerate(charts):
        z,u = layouts[i]
        for a,slack in zip(c.inequalities,u):
            _,a = a.clear_denominators()
            residuals.append(a.homogenized_lift(arity,z,q+i)-variables[slack])
        for a in c.equalities:
            _,a = a.clear_denominators()
            residuals.append(a.homogenized_lift(arity,z,q+i))
        Z = sum((variables[index] for index in z+u),Poly.const(arity,0))
        if mode == "sos":
            residuals.append((1-e[i])*Z)
        else:
            products.append((E-e[i])*Z)
    for output in range(q):
        pool = sum((c.outputs[output].homogenized_lift(arity,layouts[i][0],q+i)
                    for i,c in enumerate(charts)), Poly.const(arity,0))
        _,residual = (variables[output]-pool).clear_denominators()
        residuals.append(residual)
    expression = sum((r*r for r in residuals),Poly.const(arity,0))+sum(products,Poly.const(arity,0))
    assert expression.degree <= 4
    assert all(c.denominator == 1 for p,c in expression.terms)
    return Certificate(charts,q,tuple(names),tuple(layouts),tuple(residuals),tuple(products),expression,mode)


def binary_shuttle_charts(d):
    integer(d,"fixed gap",True)
    if d < 7:
        raise ValueError("fixed gap must be at least 7")
    n,j = Poly.var(2,0),Poly.var(2,1)
    domain = (d+n-6-j,)
    right = Chart("right",2,(n*n+(2*d-11)*n+j, Poly.const(2,0),3+j,4+j,d+n),domain)
    left = Chart("left",2,(n*n+(2*d-10)*n+d-5+j,Poly.const(2,0),d+n-4-j,d+n-2-j,d+n+1),domain)
    return right,left


def uniform_binary_shuttle(mode='sos'):
    """Specialized 8-witness certificate with external (x,t,x0,x1,x2,x3).

    Gap is 7+x, with x natural. This specializes the displayed formulas,
    rather than broadening the generic fixed-coefficient chart interface.
    The returned certificate's generic chart witness builder is not used;
    uniform_binary_witness provides its canonical witnesses instead.
    """
    if mode not in ('products','sos'):
        raise ValueError('invalid gate mode')
    q,arity=6,14
    x,t,x0,x1,x2,x3,eR,eL,nR,jR,uR,nL,jL,uL=(Poly.var(arity,k) for k in range(arity))
    d=7+x
    residuals=[eR+eL-1,
        (d-6)*eR+nR-jR-uR,
        (d-6)*eL+nL-jL-uL,
        t-(nR*nR+(2*d-11)*nR+jR+nL*nL+(2*d-10)*nL+(d-5)*eL+jL),
        x0,
        x1-(3*eR+jR+(d-4)*eL+nL-jL),
        x2-(4*eR+jR+(d-2)*eL+nL-jL),
        x3-(d*eR+nR+(d+1)*eL+nL)]
    products=[]
    if mode=='products':
        products=[eL*(nR+jR+uR),eR*(nL+jL+uL)]
    else:
        residuals.extend(((1-eR)*(nR+jR+uR),(1-eL)*(nL+jL+uL)))
    expression=sum((r*r for r in residuals),Poly.const(arity,0))+sum(products,Poly.const(arity,0))
    # No generic Chart objects are claimed here: domains involve external x.
    return Certificate((),q,('eR','eL','nR','jR','uR','nL','jL','uL'),(),
                       residuals,products,expression,mode,(0,1))


def uniform_binary_witness(x,side,n,j):
    for value,name in ((x,'gap parameter'),(side,'side'),(n,'cycle'),(j,'phase parameter')):
        integer(value,name,True)
    if side not in (0,1):
        raise ValueError('side must be 0 or 1')
    slack=1+x+n-j
    if slack<0:
        raise ValueError('phase parameter exceeds flight domain')
    if side==0:
        return (1,0,n,j,slack,0,0,0)
    return (0,1,0,0,0,n,j,slack)
