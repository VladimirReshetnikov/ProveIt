#!/usr/bin/env python3
"""Independent finite checks of identities used in the two-world HC proof.

These finite structures are NOT asserted to satisfy every K instance.
The checker validates the exact syntactic K-to-closure reduction, the
relative-existential identity, and the antichain subset identity.
The set-theoretic witness-closure argument is given in the companion proof.
"""
import itertools,json
from functools import lru_cache
from pathlib import Path

I=lambda p,q:('I',p,q)
Q=lambda i,p:('Q',i,p)
R=lambda i,j:('R',i,j)
F=R(0,0)
N=lambda p:I(p,F)
M=('M',)
D=tuple(range(3))
R0={(1,0)}
R1={(x,y)for x in D for y in D if x==y or x==(y+1)%3}
assert R0<=R1 and all((x,x)not in R0 and (x,x)in R1 for x in D)


def make_evaluator(a,b,root_mask,final_mask):
    def phi(t,p,y):return bool((root_mask if t==0 else final_mask)>>(3*p+y)&1)
    @lru_cache(None)
    def ev(f,t,v):
        if f[0]=='M':return phi(t,v[a],v[b])
        if f[0]=='R':return(v[f[1]],v[f[2]])in(R0 if t==0 else R1)
        if f[0]=='I':return not ev(f[1],t,v)or ev(f[2],t,v)
        assert f[0]=='Q'
        i,g=f[1:]
        return all(ev(g,s,v[:i]+(x,)+v[i+1:])for s in range(t,2)for x in D)
    return ev,phi


def bundle(a,b,c):
    r=R(b,c)
    s=Q(c,I(R(c,a),R(c,b)))
    w=Q(b,I(M,N(Q(b,I(M,N(r))))))
    u=Q(a,I(s,w))
    h=Q(b,I(r,N(Q(a,I(M,N(u))))))
    v=I(R(a,b),Q(c,R(a,b)))
    j=Q(c,I(h,N(w)))
    return N(I(v,j)),(s,w,u,h,j)


def expected(phi,a,b,seed):
    if a!=b:
        def W(p,C):
            return not any(phi(0,p,y)for y in D)or any(phi(0,p,y)and(y,C)in R0 for y in D)
        def H(C):
            return all(any(phi(0,p,y)for p in D)and W(y,C)for y in D if(y,C)in R0)
        return any(W(seed,C)and H(C)for C in D)
    has=any(phi(0,x,x)for x in D)
    return any((any(phi(0,x,x)and(x,C)in R0 for x in D)if has else not any((x,C)in R0 for x in D))for C in D)


def exhaustive_modal_algebra():
    """Every truth-valued function on two worlds and a 2-by-2 grid."""
    points=list(itertools.product(range(2),range(2),range(2)))
    lookup={point:i for i,point in enumerate(points)}
    full=(1<<len(points))-1
    future=sum(1<<k for k,(t,x,y)in enumerate(points)if t==1)
    reaches=[]
    for coordinate in range(2):
        masks=[]
        for t,x,y in points:
            targets=[]
            for s,z in itertools.product(range(t,2),range(2)):
                targets.append((s,z,y)if coordinate==0 else(s,x,z))
            masks.append(sum(1<<lookup[p]for p in targets))
        reaches.append(masks)
    def quant(i,A):
        return sum(1<<k for k,need in enumerate(reaches[i])if A&need==need)
    table=[[quant(i,A)for A in range(full+1)]for i in range(2)]
    imp=lambda A,B:(~A|B)&full
    neg=lambda A:imp(A,future)
    distribution=reflexivity=commutation=existential=negation=0
    for i,A in itertools.product(range(2),range(full+1)):
        assert table[i][A]&~A==0
        reflexivity+=1
        assert table[i][full]==full
        for j in range(2):
            assert table[i][table[j][A]]==table[j][table[i][A]]
            commutation+=1
        NA=neg(A)
        assert NA&future==future
        assert NA&(~future&full)==(~A)&(~future&full)
        negation+=1
        EX=neg(table[i][NA])
        for k,(t,x,y)in enumerate(points):
            if t==1:want=True
            else:
                same_world=[(0,z,y)if i==0 else(0,x,z)for z in range(2)]
                want=any(A>>(lookup[p])&1 for p in same_world)
            assert bool(EX>>k&1)==want
        existential+=1
        for B in range(full+1):
            assert imp(table[i][imp(A,B)],imp(table[i][A],table[i][B]))==full
            distribution+=1
    rho8=0
    for A,B,C,U in itertools.product([False,True],repeat=4):
        ip=lambda p,q:not p or q
        assert ip(ip(ip(C,U),A),ip(ip(A,C),ip(B,C)))
        rho8+=1
    return {
        'grid_worlds':2,'grid_coordinates':2,'values_per_coordinate':2,
        'arbitrary_formula_valuations':full+1,
        'rho8_boolean_cases':rho8,
        'distribution_cases':distribution,
        'T_reflexivity_cases':reflexivity,
        'commutation_cases':commutation,
        'native_negation_cases':negation,
        'native_existential_cases':existential,
        'theorem_generalization_of_top':True,
    }


def main():
    algebra=exhaustive_modal_algebra()
    reduction_cases=0
    for a,b,c in[(0,1,2),(0,0,2)]:
        B,parts=bundle(a,b,c)
        for root in range(512):
            for future in sorted({0,511,root,511^root}):
                ev,phi=make_evaluator(a,b,root,future)
                for seed in D:
                    vv=[0,0,0];vv[a]=seed;v=tuple(vv)
                    assert ev(B,0,v)==expected(phi,a,b,seed),(a,b,root,future,v)
                    assert ev(B,1,v)
                    assert all(ev(p,1,v)for p in parts[1:]),(a,b,root,future,v)
                    reduction_cases+=1
    existential_cases=0
    for lo,hi in itertools.product(range(8),repeat=2):
        def val(t,x):return bool((lo if t==0 else hi)>>x&1)
        final_N=[True]*3
        root_N=[not val(0,x)for x in D]
        Q_N=all(root_N+final_N)
        native_Ex=not Q_N
        assert native_Ex==any(val(0,x)for x in D)
        existential_cases+=1
    subset_cases=0
    for p,u in itertools.product(D,repeat=2):
        value=all(not(z,p)in rel or(z,u)in rel for rel in[R0,R1]for z in D)
        assert value==(p==u),(p,u)
        subset_cases+=1
    result={
        'status':'ALL_FINITE_REDUCTION_CHECKS_PASSED',
        'scope':'Checks the displayed Boolean/modal reductions, not a finite full K model and not the HC witness-closure theorem.',
        'exact_K_bundle_reduction_cases':reduction_cases,
        'relative_existential_cases':existential_cases,
        'antichain_subset_cases':subset_cases,
        'public_role_cases':['a != b','a = b'],
        'worlds':[0,1],
        'finite_domain_size':3,
        'root_relation':sorted(R0),
        'final_relation':sorted(R1),
        'exhaustive_modal_algebra':algebra,
    }
    target=Path(__file__).with_name('t_replacement_countermodel_checks.json')
    target.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
