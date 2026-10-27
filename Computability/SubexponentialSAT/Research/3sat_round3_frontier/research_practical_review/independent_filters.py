"""Independent algebra and coordinate-ring checks; no candidate-code import.

The ring is Z[U,V]/(U^2+U+1,V^ell), calculated over integers first.
"""
from itertools import product
from math import comb, factorial, prod
import json
import random


def compositions(n, t):
    if t == 0:
        if n == 0:
            yield ()
    elif t == 1:
        yield (n,)
    else:
        for a in range(n+1):
            for tail in compositions(n-a,t-1):
                yield (a,)+tail


class Integers:
    def __init__(self, ell):
        self.ell=ell
        self.zero=(0,)*(2*ell)
        self.one=(1,)+(0,)*(2*ell-1)
        self.root=(0,1)+(0,)*(2*ell-2)

    def add(self,a,b):
        return tuple(x+y for x,y in zip(a,b))

    def scale(self,a,n):
        return tuple(x*n for x in a)

    def mul(self,a,b):
        out=[0]*(2*self.ell)
        for d in range(self.ell):
            for e in range(self.ell-d):
                x,y=a[2*d:2*d+2]
                z,w=b[2*e:2*e+2]
                out[2*(d+e)] += x*z-y*w
                out[2*(d+e)+1] += x*w+y*z-y*w
        return tuple(out)

    def residue(self,a,p):
        return tuple(x % (1<<p) for x in a)


def exact_coefficient(ring, rows, beta):
    zeroexp=(0,)*len(beta)
    table={zeroexp:ring.one}
    for row in rows:
        nxt={}
        for exp,value in table.items():
            for j,c in enumerate(row):
                if exp[j]<beta[j]:
                    key=list(exp);key[j]+=1;key=tuple(key)
                    nxt[key]=ring.add(nxt.get(key,ring.zero),ring.mul(value,c))
        table=nxt
    return table.get(tuple(beta),ring.zero)


def evaluate(ring,rows,point):
    result=ring.one
    for row in rows:
        linear=ring.zero
        for c,x in zip(row,point):
            linear=ring.add(linear,ring.mul(c,x))
        result=ring.mul(result,linear)
    return result


def half_numerator(ring,rows,beta):
    result=ring.zero
    count=0
    for gamma in product(*(range(b+1) for b in beta)):
        partner=tuple(b-g for b,g in zip(beta,gamma))
        if gamma>=partner:
            continue
        point=[ring.scale(ring.one,2*g-b) for b,g in zip(beta,gamma)]
        weight=(-1)**(len(rows)-sum(gamma))*prod(comb(b,g) for b,g in zip(beta,gamma))
        result=ring.add(result,ring.scale(evaluate(ring,rows,point),weight))
        count+=1
    return result,count


def projective_numerator(ring,rows,beta):
    # Fixed last coordinate, different from candidate's minimum-beta rule.
    roots=[ring.one,ring.root,ring.mul(ring.root,ring.root)]
    total=ring.zero
    for exps in product(range(3),repeat=len(beta)-1):
        point=[roots[e] for e in exps]+[ring.one]
        phase=(-sum(e*b for e,b in zip(exps,beta)))%3
        total=ring.add(total,ring.mul(evaluate(ring,rows,point),roots[phase]))
    return total


def hybrid_numerator(ring,rows,beta):
    fixed=next((j for j,b in enumerate(beta) if b==1),0)
    active=[j for j in range(len(beta)) if j!=fixed]
    orders=[beta[j]+1 for j in active]
    cube=[ring.one,ring.root,ring.mul(ring.root,ring.root)]
    total=ring.zero
    for exps in product(*(range(m) for m in orders)):
        point=[ring.one]*len(beta)
        weight=ring.one
        for j,m,g in zip(active,orders,exps):
            if m==2:
                point[j]=ring.scale(ring.one,(-1)**g)
                weight=ring.scale(weight,(-1)**g)
            else:
                point[j]=cube[g]
                weight=ring.mul(weight,cube[(-beta[j]*g)%3])
        total=ring.add(total,ring.mul(evaluate(ring,rows,point),weight))
    return total,prod(orders)


class QuarticIntegers(Integers):
    def __init__(self):
        self.ell=1
        self.zero=(0,0,0,0)
        self.one=(1,0,0,0)
        self.root=(0,1,1,0)  # root modulo 2, NOT modulo 4.

    def mul(self,a,b):
        c=[0]*7
        for j,x in enumerate(a):
            for k,y in enumerate(b):
                c[j+k]+=x*y
        for k in range(6,3,-1):
            # U^4+U+1=0.
            c[k-4]-=c[k]
            c[k-3]-=c[k]
        return tuple(c[:4])


def monomial_filter(alpha,beta):
    ring=Integers(1)
    rows=[]
    for j,a in enumerate(alpha):
        for _ in range(a):
            rows.append([ring.one if k==j else ring.zero for k in range(len(beta))])
    return projective_numerator(ring,rows,beta)


def main():
    rng=random.Random(913772)
    counts=dict(centered_cases=0,centered_modular_checks=0,root_monomials=0,
                root_ring_cases=0,root_modular_checks=0,creation_precision_controls=0,
                hybrid_ring_cases=0,hybrid_modular_checks=0,hybrid_root_lift_controls=0)
    for t in range(1,5):
        for beta in product([1,2],repeat=t):
            R=sum(beta)
            denominator=3**(t-1)
            for alpha in compositions(R,t):
                result=monomial_filter(alpha,beta)
                expected=(denominator,0) if alpha==beta else (0,0)
                if result!=expected:
                    raise ValueError(('root monomial alias',alpha,beta,result))
                counts['root_monomials']+=1
    for ell in [1,2,3]:
        ring=Integers(ell)
        for R in range(1,8):
            for t in range(1,min(R,4)+1):
                for raw in list(compositions(R-t,t))[:5]:
                    beta=tuple(x+1 for x in raw)
                    rows=[[tuple(rng.randrange(-7,10) for _ in ring.one) for _ in beta] for _ in range(R)]
                    coeff=exact_coefficient(ring,rows,beta)
                    numerator,count=half_numerator(ring,rows,beta)
                    B=prod(factorial(b) for b in beta)
                    divisor=(1<<(R-1))*B
                    if numerator!=ring.scale(coeff,divisor):
                        raise ValueError(('centered integer identity',R,beta,ell))
                    if count!=prod(b+1 for b in beta)//2:
                        raise ValueError('half-grid count')
                    counts['centered_cases']+=1
                    shift=(divisor & -divisor).bit_length()-1
                    odd=divisor>>shift
                    for p in [1,2,5,11]:
                        # Freeze creation representatives BEFORE computing guard numerator.
                        canonical=[[ring.residue(c,p) for c in row] for row in rows]
                        guardnum,_=half_numerator(ring,canonical,beta)
                        guardnum=ring.residue(guardnum,p+shift)
                        reduced=tuple(((c>>shift)*pow(odd,-1,1<<p)) % (1<<p) for c in guardnum)
                        if reduced!=ring.residue(coeff,p):
                            raise ValueError('centered same-creation precision failure')
                        counts['centered_modular_checks']+=1
                    if max(beta)<=2:
                        numerator=projective_numerator(ring,rows,beta)
                        odd=3**(t-1)
                        if numerator!=ring.scale(coeff,odd):
                            raise ValueError('root-ring integer identity')
                        counts['root_ring_cases']+=1
                        for p in [1,2,5,11]:
                            reduced=tuple((c*pow(odd,-1,1<<p)) % (1<<p) for c in numerator)
                            if reduced!=ring.residue(coeff,p):
                                raise ValueError('root same-precision failure')
                            counts['root_modular_checks']+=1
                        numerator,denominator=hybrid_numerator(ring,rows,beta)
                        if numerator!=ring.scale(coeff,denominator):
                            raise ValueError('hybrid integer identity')
                        counts['hybrid_ring_cases']+=1
                        shift=(denominator & -denominator).bit_length()-1
                        odd=denominator>>shift
                        for p in [1,2,5,11]:
                            canonical=[[ring.residue(c,p) for c in row] for row in rows]
                            guardnum,_=hybrid_numerator(ring,canonical,beta)
                            guardnum=ring.residue(guardnum,p+shift)
                            if any(c % (1<<shift) for c in guardnum):
                                raise ValueError('hybrid sign divisibility')
                            reduced=tuple(((c>>shift)*pow(odd,-1,1<<p)) % (1<<p) for c in guardnum)
                            if reduced!=ring.residue(coeff,p):
                                raise ValueError('hybrid guard precision')
                            counts['hybrid_modular_checks']+=1
    # Wrong domain negative control: fixed exponent 3 aliases a free exponent +3.
    if monomial_filter((4,0),(1,3))!=(3,0):
        raise ValueError('alias negative control unexpectedly vanished')
    # Homogeneous coefficient 4*3^4=324 is 0 modulo 4 but 4 modulo 16.
    ring=Integers(1)
    rows=[[ring.scale(ring.one,3),ring.scale(ring.one,3)] for _ in range(4)]
    coeff=exact_coefficient(ring,rows,(3,1))
    created=ring.residue(coeff,2)
    relifted=ring.residue(created,4)
    recreated=ring.residue(coeff,4)
    if relifted==recreated:
        raise ValueError('creation precision negative control insensitive')
    counts['creation_precision_controls']+=1
    # A cubic root known only at creation precision can be arbitrarily lifted:
    # the complete sign sum supplies its 2^shift factor even for placeholders.
    ring=QuarticIntegers()
    h=ring.add(ring.add(ring.mul(ring.root,ring.root),ring.root),ring.one)
    if ring.residue(h,1)!=ring.zero or ring.residue(h,2)==ring.zero:
        raise ValueError('wrong-work-precision root control insensitive')
    for beta in [(1,1,2),(1,1,1,2),(1,1,2,2)]:
        for repeat in range(10):
            rows=[[tuple(rng.randrange(2) for _ in range(4)) for _ in beta] for _ in range(sum(beta))]
            coefficient=exact_coefficient(ring,rows,beta)
            numerator,denom=hybrid_numerator(ring,rows,beta)
            shift=(denom & -denom).bit_length()-1
            numerator=ring.residue(numerator,1+shift)
            if any(x % (1<<shift) for x in numerator):
                raise ValueError('arbitrary-root sign divisibility failed')
            result=tuple(((x>>shift)*pow(denom>>shift,-1,2))%2 for x in numerator)
            if result!=ring.residue(coefficient,1):
                raise ValueError('root creation-precision lift invariance failed')
            counts['hybrid_root_lift_controls']+=1
    return {'status':'PASS','counts':counts,
            'negative_controls':{'root_alias_outside_beta_lt_3':True,
                                 'recompute_at_later_precision_changes_tensor':True},
            'scope':'Independent integer and modular formulas; no candidate/imported executable code used.'}


if __name__=='__main__':
    print(json.dumps(main(),indent=2,sort_keys=True))
