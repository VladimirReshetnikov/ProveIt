#!/usr/bin/env python3
"""Independent symbolic and constructive audit of the oriented power graph.

This does not search for a zero of the complete consistency polynomial.
It verifies the exact finite graph translation and auxiliary arithmetic
fixtures; the universal proofs are in ORIENTED_POWER_PROOF.md.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from math import gcd, prod
from pathlib import Path

from build_equation import Builder, construct


def require(ok, message):
    if not ok:
        raise ValueError(message)


class P:
    def __init__(self, terms=None):
        self.d = {m: c for m, c in (terms or {}).items() if c}
    @staticmethod
    def atom(x):
        return P({(): x}) if isinstance(x, int) else P({(x,): 1})
    def __add__(self, q):
        if isinstance(q, int): q = P.atom(q)
        z = defaultdict(int, self.d)
        for m, c in q.d.items(): z[m] += c
        return P(z)
    __radd__ = __add__
    def __neg__(self): return P({m: -c for m, c in self.d.items()})
    def __sub__(self, q): return self + (-P.atom(q) if isinstance(q, int) else -q)
    def __rsub__(self, q): return -self + q
    def __mul__(self, q):
        if isinstance(q, int): q = P.atom(q)
        z = defaultdict(int)
        for a, x in self.d.items():
            for b, y in q.d.items(): z[tuple(sorted(a+b))] += x*y
        return P(z)
    __rmul__ = __mul__
    def __pow__(self, n):
        z = P.atom(1)
        for _ in range(n): z = z*self
        return z


def power_graph_identity():
    b = Builder(positive_powers=True)
    n, k = b.new('input.n'), b.new('input.k')
    b.power(n, k)
    values = {i: P.atom(v['name']) for i,v in enumerate(b.variables) if i not in b.gates}
    actual = {}
    for row in b.rows:
        out = row['gate']
        value = P()
        output_coefficient = 0
        for c, mon in row['terms']:
            if out is not None and out in mon:
                require(mon == [out], 'nonlinear output in defining gate')
                output_coefficient += c
                continue
            term = P.atom(c)
            for v in mon:
                require(v in values, 'gate dependency not previously evaluated')
                term = term*values[v]
            value = value+term
        if out is None:
            require(row['label'] not in actual, 'duplicate constraint label')
            actual[row['label']] = value
        else:
            require(output_coefficient == 1, 'nonmonic defining gate')
            values[out] = -value

    a = lambda s: P.atom('pow0.'+s)
    n, k, m = P.atom('input.n'), P.atom('input.k'), a('output')
    U = a('U')
    aa,z,y,q,d,g = [a('free.'+s) for s in ('a0','z0','y0','q0','d0','gap')]
    qb,qs,qr,qx = [a('quotient.'+s) for s in ('B','S','R','power')]
    W,Z,Y,T = n+k,z+1,k+y,m+g+1
    A = n+aa+1
    V,B = Y**2*(d+1),1+4*Y*(q+1)
    X = Y*(aa+1)+m+T*qx
    S,R = X+U*qs,k+4*Y*qr
    norm = lambda a,x,y: x*x+y*y-1-a*a*y*y
    expected = {
        'norm1': norm(A,X,Y), 'norm2': norm(A,U,V), 'norm3': norm(B,S,R),
        'B_mod_U': B-A-U*qb,
        'T_definition': 2*A*n-T-n*n-1,
        'last_norm': norm(W+1,A,W*Z),
    }
    require(set(actual) == {'pow0.'+s for s in expected}, 'constraint inventory differs')
    for name, polynomial in expected.items():
        require(actual['pow0.'+name].d == polynomial.d, 'exact constraint mismatch: '+name)
    require(expected['last_norm'].d == (A*A-1-W**3*(W+2)*Z*Z).d,
            'last norm identity failed')
    aux = [v['name'] for i,v in enumerate(b.variables)
           if i not in b.gates and v['name'] not in ('input.n','input.k','pow0.output')]
    require(len(aux) == 11, 'not eleven auxiliary coordinates')
    require((X+Y*n-Y*A-m-T*qx).d == {}, 'power quotient restoration identity')
    require((S-X-U*qs).d == {} and (R-k-4*Y*qr).d == {},
            'Pell quotient restoration identities')
    return {'exact_constraints': len(expected), 'eliminated_definitional_gates': len(b.gates),
            'auxiliary_coordinates': aux}


def pell(a, n):
    """Binary powering, independent of the certificate implementation."""
    D = a*a-1
    x,y,u,v = 1,0,a,1
    while n:
        if n & 1: x,y = x*u+D*y*v, x*v+y*u
        u,v = u*u+D*v*v,2*u*v
        n //= 2
    return x,y


def evaluate(b, assignments):
    values = []
    for i,v in enumerate(b.variables):
        if i not in b.gates:
            require(v['name'] in assignments, 'missing free assignment '+v['name'])
            value = assignments[v['name']]
        else:
            row = b.rows[b.gates[i]]
            coeff = sum(c for c,mon in row['terms'] if mon == [i])
            require(coeff == 1, 'gate output not monic')
            others = [(c,mon) for c,mon in row['terms'] if mon != [i]]
            require(all(j<i for c,mon in others for j in mon), 'gate not topological')
            value = -sum(c*prod(values[j] for j in mon) for c,mon in others)
        require(value >= 0, 'fixture value is negative')
        values.append(value)
    residuals = [sum(c*prod(values[j] for j in mon) for c,mon in row['terms'])
                 for row in b.rows]
    return values, residuals


def constructive_fixtures():
    cases = [(1,1),(2,1),(3,1),(4,1),(5,1),(1,2),(2,2)]
    results = []
    for n,k in cases:
        W=n+k
        A,wz=pell(W+1,W)
        require(wz%W==0,'W-divisibility fixture failed')
        Z=wz//W
        X,Y=pell(A,k)
        U,V=pell(A,2*k*Y)
        require(V>0 and V%(Y*Y)==0,'Pell-index V divisor fixture')
        require(gcd(U,4*Y)==1,'Pell-index CRT coprimality')
        B=A+U*(((1-A)*pow(U,-1,4*Y))%(4*Y))
        if B<2: B+=4*Y*U
        S,R=pell(B,k)
        T=2*A*n-n*n-1
        m=n**k
        values={'input.n':n,'input.k':k,'pow0.output':m,
                'pow0.U':U, 'pow0.free.a0':A-n-1,
                'pow0.free.z0':Z-1, 'pow0.free.y0':Y-k,
                'pow0.free.q0':(B-1)//(4*Y)-1,
                'pow0.free.d0':V//(Y*Y)-1, 'pow0.free.gap':T-m-1}
        for name,num,den in [('B',B-A,U),('S',S-X,U),('R',R-k,4*Y),
                             ('power',X+Y*n-Y*A-m,T)]:
            require(den>0 and num>=0 and num%den==0, 'oriented quotient fixture '+name)
            values['pow0.quotient.'+name]=num//den
        b=Builder(positive_powers=True)
        b.power(b.new('input.n'),b.new('input.k'))
        evaluated,residuals=evaluate(b,values)
        require(not any(residuals),'fixture does not solve graph')
        values['pow0.output']=m+1
        require(any(evaluate(b,values)[1]),'mutated output escaped')
        results.append({'base':n,'exponent':k,'maximum_witness_bit_length':max(x.bit_length() for x in evaluated)})
    return results


def positive_call_induction(root):
    source=json.loads((root/'wire_eliminated_source.json').read_text())
    b=construct(source,positive_powers=True)
    arithmetic={out:key for key,out in b.cache.items()}
    proven={}
    count=0
    for macro in b.macro_log:
        memo={}
        def lower(atom):
            if atom[0]=='c': return min(atom[1],2)
            if atom in proven: return proven[atom]
            if atom in memo: return memo[atom]
            if atom not in arithmetic: return 0
            op,a,c=arithmetic[atom]
            x,y=lower(a),lower(c)
            memo[atom]=min(x+y if op=='add' else x*y,2)
            return memo[atom]
        if macro['macro']=='power':
            require(lower(macro['base'])>=1 and lower(macro['exponent'])>=1,
                    'power call lacks positive-input certificate')
            proven[macro['output']]=1
            count+=1
        elif macro['macro']=='factorial':
            require(lower(macro['n'])>=1,'factorial argument not positive')
            proven[macro['output']]=1
        elif macro['macro']=='binomial':
            require(lower(macro['n'])>=1 and lower(macro['k'])>=1,
                    'binomial power prerequisites not positive')
        else: raise ValueError('unknown macro')
    require(count==55==len(b.powers),'unexpected power inventory')
    return {'positive_power_calls':count,'binomial_calls':len(b.binomials),
            'factorial_calls':len(b.factorials)}


def main():
    root=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=root/'ORIENTED_AUDIT.json')
    args=ap.parse_args()
    result={'status':'PASS','symbolic_power_graph':power_graph_identity(),
            'constructive_power_fixtures':constructive_fixtures(),
            'positive_call_induction':positive_call_induction(root),
            'optimized_python':not __debug__,
            'sha256':{s:sha256((root/s).read_bytes()).hexdigest()
                      for s in ['build_equation.py','direct_calculus.py','audit_oriented.py']},
            'scope':'Exact finite identities, constructive arithmetic fixtures, and positive-input induction. Universal semantic proofs and calibration remain separate.'}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__=='__main__': main()
