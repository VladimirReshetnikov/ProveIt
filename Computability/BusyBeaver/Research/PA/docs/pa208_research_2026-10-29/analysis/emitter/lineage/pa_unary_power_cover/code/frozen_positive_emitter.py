#!/usr/bin/env python3
"""Independent audit of a frozen positive power-filter emitter.

Every emitted number is a positive first-order formula. This program checks
uniform algebraic identities on finite inputs and the two exceptional formula
identities on all structures of sizes 1,2,3. It does not prove consistency,
compile a Turing machine, or claim a machine-state saving.

Run: python3 frozen_positive_emitter.py [--output results.json]
Python 3.10+, standard library only. Checks remain active under python -O.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import json
from math import isqrt
from pathlib import Path


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def pair(a, b):
    return (a+b)*(a+b+1)//2+b


def unpair(n):
    s=(isqrt(8*n+1)-1)//2
    b=n-s*(s+1)//2
    return s-b,b


class Codec:
    def __init__(self, radix=3):
        require(radix in (3,4,'dyadic','dyadic_vfirst'), 'unsupported codec')
        self.radix=radix
        self.counts=Counter()
        self.dyadic=radix in ('dyadic','dyadic_vfirst')
        self.imp_factor = 4 if self.dyadic else radix

    def op(self, kind, a, b, tag):
        self.counts[kind]+=1
        factor=(2 if kind=='R' else 4) if self.dyadic else self.radix
        if self.dyadic and kind=='I': tag=3
        if self.radix=='dyadic' and kind=='A': a,b=b,a
        return factor*pair(a,b)+tag

    def R(self,a,b): return self.op('R',a,b,0)
    def A(self,a,b): return self.op('A',a,b,1)
    def I(self,a,b): return self.op('I',a,b,2)

    def fields(self,n):
        if self.dyadic:
            if n%2==0: kind,payload='E',n//2
            elif n%4==1: kind,payload='A',(n-1)//4
            else: kind,payload='I',(n-3)//4
        else:
            payload,tag=divmod(n,self.radix)
            kind='E' if tag in (0,3) else ('A' if tag==1 else 'I')
        a,b=unpair(payload)
        if self.radix=='dyadic' and kind=='A': a,b=b,a
        return kind,a,b

    def decode(self,n):
        kind,a,b=self.fields(n)
        if kind=='E': return ('E',a,b)
        if kind=='A': return ('A',a,self.decode(b))
        return ('I',self.decode(a),self.decode(b))

    def encode(self,t):
        atom_factor=2 if self.dyadic else self.radix
        connective_factor=4 if self.dyadic else self.radix
        imp_tag=3 if self.dyadic else 2
        if t[0]=='E': return atom_factor*pair(t[1],t[2])
        if t[0]=='A':
            a,b=t[1],self.encode(t[2])
            if self.radix=='dyadic': a,b=b,a
            return connective_factor*pair(a,b)+1
        return connective_factor*pair(self.encode(t[1]),self.encode(t[2]))+imp_tag


def build_guard(c):
    return c.A(2,c.I(c.R(2,1),c.R(2,0)))


GUARDS={3:3056626,4:22224433,'dyadic':1512069,'dyadic_vfirst':1515529}


def original(n,radix=3):
    c=Codec(radix)
    e=c.R(1,n)
    s=c.A(n,c.I(c.R(n,1),c.R(n,0)))
    u=c.A(1,c.I(e,n))
    v=c.A(1,c.I(s,c.I(n,e)))
    g=c.I(c.A(n,c.I(u,c.I(v,0))),0)
    return g,dict(c.counts)


def frozen(n,radix=3,shared=True,reordered=False):
    guard=GUARDS[radix]
    c=Codec(radix)
    e=c.R(1,n)
    if shared:
        k=c.I(e+n,0)
        forward,reverse=k+c.imp_factor*n,k+c.imp_factor*e
    else:
        forward,reverse=c.I(e,n),c.I(n,e)
    u=c.A(1,forward)
    v=c.A(1,c.I(guard,reverse))
    first,second=(v,u) if reordered else (u,v)
    g=c.I(c.A(n,c.I(first,c.I(second,0))),0)
    return g,dict(c.counts)


def expected(n,radix=3,reordered=False):
    phi=Codec(radix).decode(n)
    e=('E',1,n)
    guard=('A',2,('I',('E',2,1),('E',2,0)))
    upper=('A',1,('I',e,phi))
    lower=('A',1,('I',guard,('I',phi,e)))
    q0=('E',0,0)
    first,second=(lower,upper) if reordered else (upper,lower)
    return ('I',('A',n,('I',first,('I',second,q0))),q0)


def names(t):
    if t[0]=='E': return {t[1],t[2]}
    if t[0]=='A': return {t[1]}|names(t[2])
    return names(t[1])|names(t[2])


def alpha_key(t,scope=()):
    def term(v):
        return ('b',scope.index(v)) if v in scope else ('f',v)
    if t[0]=='E': return ('E',term(t[1]),term(t[2]))
    if t[0]=='A': return ('A',alpha_key(t[2],(t[1],)+scope))
    return ('I',alpha_key(t[1],scope),alpha_key(t[2],scope))


def nodes(t):
    if t[0]=='E': return 1
    if t[0]=='A': return 1+nodes(t[2])
    return 1+nodes(t[1])+nodes(t[2])


def evaluate(t,size,relation,env):
    kind=t[0]
    if kind=='E': return bool(relation & (1 << (env[t[1]]*size+env[t[2]])))
    if kind=='I':
        return not evaluate(t[1],size,relation,env) or evaluate(t[2],size,relation,env)
    v=t[1]
    return all(evaluate(t[2],size,relation,{**env,v:a}) for a in range(size))


def low_meaning(n,size,relation,a):
    E=lambda x,y: bool(relation & (1 << (x*size+y)))
    diagonal=E(a,a)
    if n==0:
        return diagonal or any(all(not E(x,c) for x in range(size)) for c in range(size))
    universal_diagonal=all(E(x,x) for x in range(size))
    J=all(not E(x,x) or universal_diagonal for x in range(size))
    return diagonal or J


def suite():
    samples=list(range(4096))+[2**32-1,2**64,2**127+19]
    rows={}
    low_total=0
    for radix in (3,4,'dyadic','dyadic_vfirst'):
        codec=Codec(radix)
        bootstrap=Codec(radix)
        guard=build_guard(bootstrap)
        require(guard==GUARDS[radix],'cached guard mismatch')
        low_formulas={n:codec.decode(frozen(n,radix)[0]) for n in (0,1)}
        low_originals={n:codec.decode(original(n,radix)[0]) for n in (0,1)}
        low_reordered={n:codec.decode(frozen(n,radix,reordered=True)[0]) for n in (0,1)}
        largest_bits=0
        for n in samples:
            formula=codec.decode(n)
            require(max(names(formula)) <= n,'weak variable bound failed')
            if n:
                require(max(names(formula)) < n,'strict variable bound failed')
            canonical=codec.encode(formula)
            require(codec.decode(canonical)==formula,'canonical roundtrip failed')
            if radix in (3,'dyadic','dyadic_vfirst'): require(canonical==n,'bijective codec failed')
            old,old_count=original(n,radix)
            direct,direct_count=frozen(n,radix,shared=False)
            optimized,new_count=frozen(n,radix)
            require(direct==optimized,'shared opposite implication identity failed')
            tree=codec.decode(optimized)
            require(tree==expected(n,radix),'independent AST identity failed')
            require(nodes(tree)==17+2*nodes(formula),'tree size law failed')
            reordered=codec.decode(frozen(n,radix,reordered=True)[0])
            if radix=='dyadic':
                require(emit(n)==emit_polynomial(n)==emit_registers(n)==
                        frozen(n,radix,reordered=True)[0],
                        'public/polynomial/register/reference emitter mismatch')
            require(reordered==expected(n,radix,reordered=True),'reordered AST identity failed')
            require(old_count=={'R':3,'I':7,'A':4},'original count failed')
            require(direct_count=={'R':1,'I':6,'A':3},'frozen count failed')
            require(new_count=={'R':1,'I':5,'A':3},'new count failed')
            if n>=2:
                require(alpha_key(codec.decode(old))==alpha_key(tree),'regular alpha equivalence failed')
            # The outer implication and universal recover exactly the input.
            kind,outer,left_target=codec.fields(optimized)
            require(kind=='I' and left_target==0,'outer wrapper parse failed')
            kind,output_label,body=codec.fields(outer)
            require(kind=='A' and output_label==n,'raw generator index recovery failed')
            largest_bits=max(largest_bits,optimized.bit_length())
        per_size=[]
        for size in (1,2,3):
            cases=0
            for rel in range(1<<(size*size)):
                for a,n in product(range(size),(0,1)):
                    env={0:a,1:0,2:0}
                    lhs=evaluate(low_formulas[n],size,rel,env)
                    rhs=low_meaning(n,size,rel,a)
                    old=evaluate(low_originals[n],size,rel,env)
                    new_order=evaluate(low_reordered[n],size,rel,env)
                    require(lhs==rhs==old==new_order,'exceptional collision identity failed')
                    cases+=1
            per_size.append({'size':size,'structures':1<<(size*size),'formula_assignment_cases':cases})
            low_total+=cases
        _,new_count=frozen(0,radix)
        rows[str(radix)]={
            'guard':guard,'guard_bits':guard.bit_length(),
            'guard_initialization':dict(bootstrap.counts),
            'original_dynamic_pairings':14,'frozen_dynamic_pairings':10,
            'shared_frozen_dynamic_pairings':9,'shared_frozen_ledger':new_count,
            'checks_per_variant_inputs':len(samples),
            'low_collision_exhaustive':per_size,
            'largest_sample_output_bits':largest_bits,
            'code_bits_at_1000':frozen(1000,radix)[0].bit_length(),
            'reordered_code_bits_at_1000':frozen(1000,radix,reordered=True)[0].bit_length(),
            'reordered_dynamic_ledger':frozen(1000,radix,reordered=True)[1],
        }
    codecs=(3,4,'dyadic','dyadic_vfirst')
    matched={str(r):{'sum_matrix_code_bits':0,'sum_axiom_code_bits':0,
                     'dyadic_shorter':0,'same_length':0,'dyadic_longer':0} for r in codecs}
    matrix_samples=list(range(512))+[1000,2**16-1]
    for matrix_index in matrix_samples:
        phi=Codec('dyadic').decode(matrix_index)
        main_axiom=emit(matrix_index)
        target_key=alpha_key(Codec('dyadic').decode(main_axiom))
        for r in codecs:
            n=Codec(r).encode(phi)
            g=frozen(n,r,reordered=True)[0]
            require(alpha_key(Codec(r).decode(g))==target_key,
                    'matched-matrix cross-codec alpha identity failed')
            row=matched[str(r)]
            row['sum_matrix_code_bits']+=n.bit_length()
            row['sum_axiom_code_bits']+=g.bit_length()
            if main_axiom.bit_length()<g.bit_length(): row['dyadic_shorter']+=1
            elif main_axiom.bit_length()==g.bit_length(): row['same_length']+=1
            else: row['dyadic_longer']+=1
    return {
        'status':'passed','variants':rows,'total_low_collision_cases':low_total,
        'division_free_emitter':{'nonlinear_multiplications':9,
            'fixed_factors':'2 and 4, implementable by shifts/additions',
            'persistent_arithmetic_registers':3,
            'excluded_workspace':'multiplication and expression-evaluation scratch',
            'checks':4099,'runtime_formula_decoding':False,'division':False},
        'matched_formula_comparison':{'matrix_count':len(matrix_samples),
            'selection':'preferred dyadic codes 0..511,1000,65535',
            'variants':matched,
            'scope':'same named matrices re-encoded; output axioms compared up to alpha equivalence'},
        'ordinary_inputs':[0,4095],'additional_inputs':['2^32-1','2^64','2^127+19'],
        'uniform_claims_supplemented':['opposite implications share one Cantor evaluation',
            'all nonexceptional old/frozen outputs are alpha equivalent',
            'both exceptional outputs have the same classical meaning',
            'g(n) has input-recoverable output binder and size 17+2|decode(n)|'],
        'limits':['no literal Turing machine','no machine-state saving proved',
            'no full PA interpretation formalization','finite tests supplement explicit mathematical identities'],
    }


# Recommended public interface: a dyadic bijection, body-first quantifier
# pairing, lower-first clause order, and one cached 21-bit subset guard.
GUARD=GUARDS['dyadic']

def R(i,j): return 2*pair(i,j)
def A(v,body): return 4*pair(body,v)+1
def I(left,right): return 4*pair(left,right)+3

def emit(n):
    if type(n) is not int or n<0:
        raise ValueError('expected a nonnegative integer')
    e=R(1,n)
    h=I(e+n,0)
    u=A(1,h+4*n)
    v=A(1,I(GUARD,h+4*e))
    return I(A(n,I(v,I(u,0))),0)

def Q(s):
    """Quadratic primitive: one nonlinear multiply plus a left shift."""
    return 2*s*(s+1)


def emit_polynomial(n):
    """Division-free straight-line arithmetic; caller supplies n in N.

    Exactly one product in e and eight calls of Q. Fixed factors 2 and 4
    may be shifts/additions. No test, decoding, substitution, or division.
    """
    e=n*(n+5)+2
    h=Q(e+n)+3
    u=Q(h+4*n+1)+5
    j=h+4*e
    ell=Q(GUARD+j)+4*j+3
    v=Q(ell+1)+5
    c=Q(u)+3
    b=Q(v+c)+4*c+3
    z=Q(b+n)+4*n+1
    return Q(z)+3


def emit_registers(n):
    """Same polynomial with three persistent arithmetic registers.

    Multiplication and expression-evaluation workspace is excluded from
    this high-level register count. This is not a three-counter machine.
    """
    r0=n
    r1=r0*(r0+5)+2
    r2=Q(r1+r0)+3
    r1=r2+4*r1
    r2=Q(r2+4*r0+1)+5
    r1=Q(GUARD+r1)+4*r1+3
    r1=Q(r1+1)+5
    r2=Q(r2)+3
    r1=Q(r1+r2)+4*r2+3
    r1=Q(r1+r0)+4*r0+1
    r1=Q(r1)+3
    return r1


def decode(n): return Codec('dyadic').decode(n)
def encode(tree): return Codec('dyadic').encode(tree)
def fields(n): return Codec('dyadic').fields(n)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    result=suite()
    txt=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(txt,encoding='utf-8')
    print(txt,end='')

if __name__=='__main__': main()
