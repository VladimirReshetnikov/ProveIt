#!/usr/bin/env python3
"""Independent standard-library checker. Does not import the generator.

Checks an exported natural witness, every sparse quadratic residual, canonical
fraction encodings, and decoded group-inverse/moment identities. It is not a
formal verification of the compiler and does not check complete positivity.
"""
from __future__ import annotations
from fractions import Fraction
from math import gcd
from pathlib import Path
import json
import sys


def evaluate(residual, values):
    total=0
    for coefficient,indices in residual:
        if not isinstance(coefficient,int) or len(indices)>2:
            raise ValueError('Malformed quadratic residual')
        term=coefficient
        for i in indices:
            if not isinstance(i,int) or i<0 or i>=len(values):
                raise ValueError('Invalid variable index')
            term*=values[i]
        total+=term
    return total


def add(a,b):
    return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]


def mul(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def check(data):
    if data.get('format')!='canonical-quartic-v1':
        raise ValueError('Unknown certificate format')
    values=data['witness']; size=len(values)
    if size!=len(data['variables']) or any(type(v) is not int or v<0 for v in values):
        raise ValueError('Witness is not a natural tuple of the declared length')
    for i,residual in enumerate(data['residuals']):
        if evaluate(residual,values):
            raise ValueError(f'Nonzero residual {i}')
    wires={}
    for name,indices in data['rational_wires'].items():
        if len(indices)!=7 or any(i<0 or i>=size for i in indices):
            raise ValueError('Invalid rational wire indices')
        p,m,h,u,vp,vm,s=(values[i] for i in indices)
        n=p-m; d=h+1; v=vp-vm
        if not(p*m==0 and vp*vm==0 and n*u-d*v==1 and u+s==h):
            raise ValueError(f'Noncanonical wire {name}')
        if gcd(n,d)!=1 or not 0<=u<d:
            raise ValueError(f'Unreduced wire {name}')
        wires[name]=Fraction(n,d)
    meta=data['metadata']
    def matrix(key):
        return [[wires[name] for name in row] for row in meta[key]]
    t=matrix('T'); g=matrix('G'); p=matrix('P'); d=len(t)
    eye=[[Fraction(i==j) for j in range(d)] for i in range(d)]
    zero=[[Fraction(0) for j in range(d)] for i in range(d)]
    a=[[eye[i][j]-t[i][j] for j in range(d)] for i in range(d)]
    if not(add(mul(a,g),p)==eye and add(mul(g,a),p)==eye
           and mul(a,p)==zero and mul(g,p)==zero):
        raise ValueError('Decoded group-inverse equations fail')
    moment_checks=0
    if 'moments' in meta:
        x=matrix('x'); exits=matrix('exits'); ell=matrix('ell'); v=mul(g,x)
        for k,wire_matrix in enumerate(meta['moments']):
            claimed=[[wires[name] for name in row] for row in wire_matrix]
            if mul(exits,v)!=claimed:
                raise ValueError(f'Decoded factorial moment {k} fails')
            moment_checks+=1; v=mul(g,mul(t,v))
        if mul(ell,mul(p,x))!=matrix('nontermination'):
            raise ValueError('Decoded nontermination probability fails')
    if 'all_moments_recurrence' in meta:
        coefficients=[wires[name] for name in meta['all_moments_recurrence']]
        if len(coefficients)!=d+1 or coefficients[0]!=1:
            raise ValueError('Malformed all-moments recurrence')
        h=mul(t,g); b=eye
        for k in range(1,d+1):
            product=mul(h,b)
            ck=-sum(product[i][i] for i in range(d))/k
            if ck!=coefficients[k]:
                raise ValueError('Incorrect characteristic coefficient')
            b=[[product[i][j]+(ck if i==j else 0) for j in range(d)] for i in range(d)]
        if b!=zero:
            raise ValueError('Cayley-Hamilton residual is nonzero')
    return dict(natural_variables=size,residuals_checked=len(data['residuals']),
                rational_wires_checked=len(wires),matrix_identities_checked=4,
                moment_columns_checked=moment_checks)


def main():
    if len(sys.argv)!=2:
        raise SystemExit('Usage: python verify_certificate.py certificate.json')
    try:
        result=check(json.loads(Path(sys.argv[1]).read_text()))
    except (ValueError,KeyError,TypeError,IndexError) as exc:
        raise SystemExit(f'FAIL: {exc}') from exc
    print(json.dumps(dict(status='PASS',**result),indent=2))


if __name__=='__main__':
    main()
