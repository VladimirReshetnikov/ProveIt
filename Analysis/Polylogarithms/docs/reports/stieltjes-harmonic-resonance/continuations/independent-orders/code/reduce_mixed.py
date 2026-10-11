#!/usr/bin/env python3
"""Exact finite reduction of weighted colored sums with integer inner orders.

For integer a_j, positive integer p_j, and exact nonzero colors |X_j|<=1,
reduce
    sum_{m_j>=1} prod(X_j**m_j / m_j**a_j) / (sum p_j*m_j)**C
into a finite linear combination of nested polylogarithms whose first
order is C plus an integer and whose remaining orders are positive integers.

The algorithm implements root filtering, exact sparse integral shuffles,
local partial fractions at repeated poles, coefficient convolution, and
recursive elimination of nonpositive inner slots. All coefficients are
SymPy exact expressions. No floating-point period evaluation, PSLQ,
nonzero tolerance, or arithmetic-independence assumption is used.

The returned cumulative colors are the products of successive relative
MPL colors. They stay in the input's root-filtered alphabet. Relative
colors can have modulus greater than one; cumulative colors govern the
nested-series convergence. For boundary colors, the identity is first
proved in a common half-plane and then interpreted by meromorphic
continuation in C. Integer inner orders are fixed, not differentiable
parameters of this finite identity.

CLI:
    python reduce_mixed.py --input input.json --output reduction.json
Input shape:
    {"orders":[1,1,-2],"colors":["1/2","1/2","1/2"],"weights":[1,1,1]}

The exact-expression simplifier can be costly for large algebraic root
alphabets. This is an executable proof-of-concept compiler, not a claim
of optimal complexity. Requires Python 3.10+ and SymPy.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
from math import comb
from pathlib import Path
from typing import Iterable
import argparse
import json
import sympy as sp

Expr = sp.Expr
Word = tuple[Expr | None, ...]  # None=dt/t; alpha=alpha*dt/(1-alpha*t).

@lru_cache(maxsize=50000)
def normal(value: Expr) -> Expr:
    value = sp.sympify(value)
    if value.is_Rational:
        return value
    # The values here are exact numeric colors/coefficient expressions;
    # no free integration or spectral variable is normalized this way.
    return sp.simplify(sp.expand_complex(value))


def same(a: Expr, b: Expr) -> bool:
    return normal(a-b) == 0


@dataclass(frozen=True)
class MPL:
    """Li_{C+offset,inner...} with cumulative alphabet letters."""
    offset: int
    inner: tuple[int, ...]
    alphabet: tuple[Expr, ...]

    def __post_init__(self):
        if len(self.alphabet) != len(self.inner)+1:
            raise ValueError("MPL alphabet/index length mismatch")

    @property
    def depth(self) -> int:
        return len(self.alphabet)

    @property
    def relative_colors(self) -> tuple[Expr, ...]:
        return (self.alphabet[0],) + tuple(
            normal(b/a) for a,b in zip(self.alphabet,self.alphabet[1:]))


Polynomial = dict[MPL, Expr]


def add(out: Polynomial, term: MPL, coefficient: Expr) -> None:
    coefficient = normal(out.get(term,sp.S.Zero)+coefficient)
    if coefficient == 0:
        out.pop(term,None)
    else:
        out[term]=coefficient


def scaled_add(out: Polynomial, part: Polynomial, coefficient: Expr) -> None:
    for term,c in part.items():
        add(out,term,coefficient*c)


@lru_cache(maxsize=30000)
def shuffle(u: Word, v: Word) -> dict[Word, int]:
    if not u:
        return {v:1}
    if not v:
        return {u:1}
    out: dict[Word,int] = {}
    for w,c in shuffle(u[1:],v).items():
        key=(u[0],)+w
        out[key]=out.get(key,0)+c
    for w,c in shuffle(u,v[1:]).items():
        key=(v[0],)+w
        out[key]=out.get(key,0)+c
    return out


def positive_product(factors: list[tuple[int,Expr]]) -> dict[Word,int]:
    out: dict[Word,int] = {():1}
    for order,color in factors:
        word=(None,)*(order-1)+(color,)
        nxt: dict[Word,int] = {}
        for w,c in out.items():
            for v,m in shuffle(w,word).items():
                nxt[v]=nxt.get(v,0)+c*m
        out=nxt
    return out


def decode_word(word: Word) -> tuple[tuple[int,...],tuple[Expr,...]]:
    indices=[]
    alphabet=[]
    order=1
    for letter in word:
        if letter is None:
            order+=1
        else:
            indices.append(order)
            alphabet.append(letter)
            order=1
    if order!=1 or not indices:
        raise ValueError("Expected a nonempty word ending in a nonzero letter")
    return tuple(indices),tuple(alphabet)


@lru_cache(maxsize=None)
def negative_numerator(M: int) -> tuple[Expr,...]:
    """N_M(z) with Li_{-M}(z)=N_M(z)/(1-z)^(M+1)."""
    # N_0=z; applying z*d/dz gives
    # N_{M+1}=z*((1-z)*N_M' + (M+1)*N_M).
    coefficients=[sp.S.Zero,sp.S.One]
    for h in range(M):
        nxt=[sp.S.Zero]*(len(coefficients)+1)
        for j,c in enumerate(coefficients):
            if j:
                nxt[j]+=j*c
                nxt[j+1]-=j*c
            nxt[j+1]+=(h+1)*c
        while len(nxt)>1 and nxt[-1]==0:
            nxt.pop()
        coefficients=nxt
    return tuple(coefficients)


def truncated_multiply(a: list[Expr], b: list[Expr], N: int) -> list[Expr]:
    out=[sp.S.Zero]*N
    for j,x in enumerate(a[:N]):
        if x==0:
            continue
        for k,y in enumerate(b[:N-j]):
            if y!=0:
                out[j+k]+=x*y
    return [normal(x) for x in out]


def rational_partial_fractions(
    factors: list[tuple[int,Expr]],
) -> tuple[Expr,list[tuple[Expr,int,Expr]]]:
    """R=c_inf+sum c_(alpha,h)/(1-alpha*t)^h.

    Input factors are (M,alpha), meaning Li_{-M}(alpha*t).
    For M_alpha=sum_(beta=alpha)(M_beta+1), coefficients are exactly
        c_(alpha,h)=[u^(M_alpha-h)] u^M_alpha R((1-u)/alpha).
    The Taylor product below cancels coincident denominator factors
    before expansion, so no spurious 0/0 occurs at repeated colors.
    """
    if not factors:
        return sp.S.One,[]
    alphabets=[]
    for _,alpha in factors:
        if not any(same(alpha,beta) for beta in alphabets):
            alphabets.append(alpha)
    poles=[]
    for alpha in alphabets:
        multiplicity=sum(M+1 for M,beta in factors if same(alpha,beta))
        series=[sp.S.One]+[sp.S.Zero]*(multiplicity-1)
        for M,beta in factors:
            ratio=normal(beta/alpha)
            # Numerator N_M(ratio*(1-u)), expanded exactly.
            numerator=[sp.S.Zero]*multiplicity
            for j,c in enumerate(negative_numerator(M)):
                for k in range(min(j,multiplicity-1)+1):
                    numerator[k]+=c*ratio**j*(-1)**k*comb(j,k)
            series=truncated_multiply(series,[normal(x) for x in numerator],multiplicity)
            if not same(beta,alpha):
                # (1-ratio+ratio*u)^(-M-1).
                denom=[normal((-1)**k*comb(M+k,k)*ratio**k/
                              (1-ratio)**(M+1+k))
                       for k in range(multiplicity)]
                series=truncated_multiply(series,denom,multiplicity)
        for h in range(1,multiplicity+1):
            coefficient=normal(series[multiplicity-h])
            if coefficient!=0:
                poles.append((alpha,h,coefficient))
    c_infty=sp.Integer((-1)**len(factors)) if all(M==0 for M,_ in factors) else sp.S.Zero
    if normal(c_infty+sum(c for _,_,c in poles))!=0:
        raise ArithmeticError("Partial fractions do not preserve R(0)=0")
    return c_infty,poles


@lru_cache(maxsize=None)
def binomial_coefficients(h: int) -> tuple[Expr,...]:
    """Coefficients b_(h,k) of binom(v+h-1,h-1)."""
    out=[sp.S.One]
    for j in range(1,h):
        nxt=[sp.S.Zero]*(len(out)+1)
        for k,c in enumerate(out):
            nxt[k]+=c
            nxt[k+1]+=c/sp.Integer(j)
        out=nxt
    return tuple(out)


@lru_cache(maxsize=10000)
def geometric_moment(h: int,q: Expr) -> Expr:
    """(q*d/dq)^h 1/(1-q), as a rational function at q!=1."""
    if h==0:
        return normal(1/(1-q))
    return normal(sum(c*q**j for j,c in enumerate(negative_numerator(h))) /
                  (1-q)**(h+1))


def remove_slot(term: MPL,j: int,shift: int,upper: bool) -> MPL:
    """Remove inner position j (0-based), shifting its chosen neighbor.

    Upper term q^U: delete cumulative letter j-1 and shift index j-1.
    Lower term q^L: delete cumulative letter j and shift index j+1;
    at the final slot the lower endpoint is constant L=0.
    """
    indices=[term.offset,*term.inner]
    letters=list(term.alphabet)
    if upper:
        indices[j-1]-=shift
        del letters[j-1]
    else:
        if j+1<len(indices):
            indices[j+1]-=shift
        elif shift:
            raise ValueError("Cannot shift the fixed lower endpoint zero")
        del letters[j]
    del indices[j]
    return MPL(int(indices[0]),tuple(int(k) for k in indices[1:]),tuple(letters))


@lru_cache(maxsize=30000)
def eliminate(term: MPL) -> Polynomial:
    """Eliminate all nonpositive inner indices; outer C+offset stays free."""
    bad=next((j for j,a in enumerate(term.inner,1) if a<=0),None)
    if bad is None:
        return {term:sp.S.One}
    j=bad
    M=-term.inner[j-1]
    q=normal(term.alphabet[j]/term.alphabet[j-1])
    at_end=j==term.depth-1
    raw: Polynomial={}
    if same(q,sp.S.One):
        # Exact confluent rule [B_(M+1)(U)-B_(M+1)(L+1)]/(M+1).
        x=sp.Symbol('_mixed_bernoulli_variable')
        upper=sp.Poly(sp.bernoulli(M+1,x)/sp.Integer(M+1),x)
        lower=sp.Poly(-sp.bernoulli(M+1,x+1)/sp.Integer(M+1),x)
        for (power,),c in upper.terms():
            add(raw,remove_slot(term,j,power,True),c)
        if at_end:
            add(raw,remove_slot(term,j,0,False),lower.eval(0))
        else:
            for (power,),c in lower.terms():
                add(raw,remove_slot(term,j,power,False),c)
    else:
        # Difference of the two rational geometric-moment tails.
        for h in range(M+1):
            degree=M-h
            coefficient=comb(M,h)*geometric_moment(h,q)
            add(raw,remove_slot(term,j,degree,True),-coefficient)
            if at_end:
                add(raw,remove_slot(term,j,0,False),coefficient*q)
            else:
                for power in range(degree+1):
                    add(raw,remove_slot(term,j,power,False),
                        coefficient*q*comb(degree,power))
    out: Polynomial={}
    for smaller,c in raw.items():
        if smaller.depth>=term.depth:
            raise ArithmeticError("Elimination did not decrease depth")
        scaled_add(out,eliminate(smaller),c)
    return out


def roots_of_color(color: Expr,p: int) -> tuple[Expr,...]:
    if p==1:
        return (normal(color),)
    root=sp.root(color,p)
    roots=tuple(normal(root*sp.exp(2*sp.pi*sp.I*k/p)) for k in range(p))
    if any(normal(alpha**p-color)!=0 for alpha in roots):
        raise ValueError("SymPy could not certify this root alphabet exactly")
    if any(same(roots[j],roots[k]) for j in range(p) for k in range(j)):
        raise ValueError("Root enumeration has a repeated root")
    return roots


def reduce_unweighted(orders: tuple[int,...],colors: tuple[Expr,...]) -> Polynomial:
    positives=[(a,x) for a,x in zip(orders,colors) if a>0]
    negatives=[(-a,x) for a,x in zip(orders,colors) if a<=0]
    c_infty,poles=rational_partial_fractions(negatives)
    out: Polynomial={}
    if not positives:
        for alpha,h,c in poles:
            for k,b in enumerate(binomial_coefficients(h)):
                add(out,MPL(-k,(),(alpha,)),c*b)
        return out
    for word,multiplicity in positive_product(positives).items():
        indices,alphabet=decode_word(word)
        k1,*inner=indices
        base=MPL(k1,tuple(inner),alphabet)
        add(out,base,multiplicity*c_infty)
        for alpha,h,c in poles:
            add(out,base,multiplicity*c)
            for k,b in enumerate(binomial_coefficients(h)):
                for j in range(k+1):
                    inserted=MPL(-k+j,(k1-j,*inner),(alpha,*alphabet))
                    coefficient=multiplicity*c*b*(-1)**j*comb(k,j)
                    scaled_add(out,eliminate(inserted),coefficient)
    return out


def reduce_mixed(
    orders: Iterable[int], colors: Iterable[Expr], weights: Iterable[int] | None=None,
) -> Polynomial:
    orders=tuple(orders)
    colors=tuple(normal(sp.sympify(x,locals={'I':sp.I})) for x in colors)
    weights=tuple(weights) if weights is not None else (1,)*len(orders)
    if not orders or not (len(orders)==len(colors)==len(weights)):
        raise ValueError("Nonempty orders, colors, weights must have equal lengths")
    if any(not isinstance(a,int) for a in orders):
        raise ValueError("Every inner order must be a Python integer")
    if any(not isinstance(p,int) or p<=0 for p in weights):
        raise ValueError("Every weight must be a positive Python integer")
    if any(x.free_symbols or x==0 or not x.is_number or x.has(sp.Float)
           or x in (sp.oo,-sp.oo,sp.zoo,sp.nan) for x in colors):
        raise ValueError("Colors must be exact finite nonzero numeric expressions; use rational strings rather than floats")
    for x in colors:
        outside=sp.simplify(sp.Abs(x)>1)
        if outside==sp.S.true:
            raise ValueError("The stated theorem requires |X_j|<=1")
        if outside!=sp.S.false:
            raise ValueError("SymPy could not certify |X_j|<=1 for this exact expression")
    alphabets=[roots_of_color(x,p) for x,p in zip(colors,weights)]
    coefficient=sp.prod(sp.Integer(p)**(a-1) for a,p in zip(orders,weights))
    out: Polynomial={}
    for chosen in product(*alphabets):
        scaled_add(out,reduce_unweighted(orders,chosen),coefficient)
    P=sum(a>0 for a in orders)
    bound=P if P==len(orders) else P+1
    alphabet=[alpha for group in alphabets for alpha in group]
    for term in out:
        if any(k<=0 for k in term.inner) or term.depth>bound:
            raise ArithmeticError("Output violates the positive-inner/depth invariant")
        if any(not any(same(alpha,beta) for beta in alphabet) for alpha in term.alphabet):
            raise ArithmeticError("Output leaves the cumulative root alphabet")
    return out


def serialize(reduction: Polynomial) -> list[dict]:
    terms=sorted(reduction,key=lambda t:(t.depth,t.offset,t.inner,tuple(map(str,t.alphabet))))
    return [{'coefficient':str(reduction[t]),'first_order_offset':t.offset,
             'inner_orders':list(t.inner),'cumulative_colors':list(map(str,t.alphabet)),
             'relative_colors':list(map(str,t.relative_colors))} for t in terms]


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input',required=True,type=Path)
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    data=json.loads(args.input.read_text())
    result=reduce_mixed(data['orders'],data['colors'],data.get('weights'))
    P=sum(a>0 for a in data['orders'])
    record={'schema':'proveit.mixed-integer-orders.v1','input':data,
            'first_order':'C + first_order_offset','terms':serialize(result),
            'term_count':len(result),'depth_bound':P if P==len(data['orders']) else P+1,
            'identity_scope':'Finite exact coefficient identity, hence meromorphic identity in C; fixed C-derivatives are permitted.'}
    text=json.dumps(record,indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text)
    else:
        print(text,end='')


if __name__=='__main__':
    main()
