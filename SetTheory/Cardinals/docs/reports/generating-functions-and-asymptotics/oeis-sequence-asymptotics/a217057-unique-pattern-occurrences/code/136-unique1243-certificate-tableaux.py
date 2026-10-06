"""Exact three-row computations and finite algebra/analytic diagnostics.

All arithmetic used for acceptance and the output is integer or Fraction.
This module imports only the Python standard library.
"""
from functools import lru_cache
from fractions import Fraction
from itertools import permutations, product
from math import comb, factorial


def need(condition, message):
    if not condition:
        raise ValueError(message)


@lru_cache(None)
def partitions(n):
    return tuple((n-b-c,b,c) for c in range(n//3+1)
                 for b in range(c,(n-c)//2+1))


@lru_cache(None)
def dimension(shape):
    a,b,c = shape
    need(a >= b >= c >= 0, "hook argument is not a partition")
    num = factorial(a+b+c)*(a-b+1)*(a-c+2)*(b-c+1)
    den = factorial(a+2)*factorial(b+1)*factorial(c)
    value, remainder = divmod(num, den)
    need(remainder == 0 and value > 0, "hook integrality")
    return value


@lru_cache(None)
def corner_dimension(shape):
    """Independent dimension: remove each possible corner, no hook formula."""
    if shape == (0,0,0):
        return 1
    answer = 0
    for row in range(3):
        if shape[row] > (shape[row+1] if row < 2 else 0):
            child = list(shape)
            child[row] -= 1
            answer += corner_dimension(tuple(child))
    need(answer > 0, "corner recursion shape")
    return answer


def interlaces(outer, inner):
    a,b,c = outer
    u,v,w = inner
    return a >= u >= b >= v >= c >= w >= 0


def horizontal_cells(outer, inner):
    """Independent strip test by the actual removed cell columns."""
    if not (outer[0] >= outer[1] >= outer[2] >= 0 and
            inner[0] >= inner[1] >= inner[2] >= 0):
        return False
    if any(inner[i] > outer[i] for i in range(3)):
        return False
    columns = [j for i in range(3) for j in range(inner[i]+1,outer[i]+1)]
    return len(columns) == len(set(columns))


@lru_cache(None)
def F(m):
    matrix = [[0]*(m+1) for _ in range(m+1)]
    for a,b,c in partitions(m):
        weights = [0]*(m+1)
        for u in range(b,a+1):
            for v in range(c,b+1):
                for w in range(c+1):
                    weights[m-u-v-w] += dimension((u,v,w))
        need(weights[0] == dimension((a,b,c)), "zero strip")
        for p,x in enumerate(weights):
            for q,y in enumerate(weights):
                matrix[p][q] += x*y
    return tuple(tuple(row) for row in matrix)


@lru_cache(None)
def H(h):
    current, previous = F(h+2), F(h+1)
    result = {}
    for i in range(h+2):
        for j in range(h+2):
            value = current[i+1][j+1]-previous[i][j]
            need(value >= 0, "H positivity")
            need(i+j <= h or value == 0, "H triangular support")
            if i+j <= h:
                result[i,j] = value
    return result


@lru_cache(None)
def J(k,s):
    return sum(H(k+s)[k,j] for j in range(s+1))


def spine(n):
    return sum(J(k,s)*J(k,n-4-k-s)
               for k in range(max(n-3,0)) for s in range(n-3-k))


def triangular_partial(cutoff):
    value = Fraction(0)
    rows = []
    for h in range(cutoff+1):
        increment = sum((Fraction(J(k,h-k)*(5*k+24)*(k+2),972*3**k*9**(h-k))
                         for k in range(h+1)), Fraction(0))
        need(increment > 0, "positive amplitude increment")
        value += increment
        if h % 5 == 0 or h == cutoff:
            rows.append({"cutoff":h,"lower_fraction":str(value)})
    return {"cutoff":cutoff,"summands":(cutoff+1)*(cutoff+2)//2,
            "lower_fraction":str(value),"rows":rows,
            "scope":"Positive finite lower bound only; no error bound or certified decimal for full R"}


def B(a,b):
    """[z^b](1+z)^a for ALL integer a,b."""
    if b < 0:
        return 0
    if a >= 0:
        return comb(a,b) if b <= a else 0
    return (-1)**b*comb(b-a-1,b)


def hstep(r):
    return B(r,r)


def delta(r):
    return B(0,r)


SIGNS = tuple((p,(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3)))
              for p in permutations(range(1,4)))


@lru_cache(None)
def D(shape):
    m = sum(shape)
    answer = 0
    for sigma, sign in SIGNS:
        e = [shape[i]-(i+1)+sigma[i] for i in range(3)]
        answer += sign*B(m,e[0])*B(m-e[0],e[1])*B(e[2],e[2])
    return answer


def I(outer,inner):
    a,b,c = outer
    u,v,w = inner
    return hstep(a-u)*hstep(u-b)*hstep(b-v)*hstep(v-c)*hstep(c-w)*hstep(w)


@lru_cache(None)
def encoded_F(m,p,q,N):
    """Delta-pruned box sum of E, not a literal (N+1)^9 enumeration.

Generate every box triple with a required sum, then use the actual
binomial I and D expressions. No partition generator or F is used here.
The product of the two strip sums is distributivity of E's mu,nu sum.
"""
    def box_triples(total):
        return [(a,b,total-a-b) for a in range(N+1) for b in range(N+1)
                if 0 <= total-a-b <= N]
    outers = box_triples(m)
    left, right = box_triples(m-p), box_triples(m-q)
    return sum(sum(I(lam,mu)*D(mu) for mu in left)*
               sum(I(lam,nu)*D(nu) for nu in right) for lam in outers)


def algebra_checks(max_n=10):
    for r in range(-12,13):
        need(hstep(r) == int(r >= 0), "B step")
        need(delta(r) == int(r == 0), "B delta")
    # Pascal's identity includes negative upper and lower arguments.
    primitive_cases = 0
    for a in range(-8,9):
        for b in range(-8,9):
            need(B(a,b) == B(a-1,b)+B(a-1,b-1), "generalized Pascal")
            primitive_cases += 1
    arbitrary_D_cases = 0
    for shape in product(range(-3,7),repeat=3):
        need(type(D(shape)) is int, "everywhere-defined D")
        arbitrary_D_cases += 1
    strip_cases = 0
    triples = tuple(product(range(-1,3),repeat=3))
    for outer in triples:
        for inner in triples:
            need(I(outer,inner) == int(horizontal_cells(outer,inner)), "binomial strip indicator")
            strip_cases += 1
    rows = []
    expanded_products = 0
    for n in range(max_n+1):
        N=n+2
        total=0
        for k in range(max(n-3,0)):
            for s in range(n-3-k):
                t=n-4-k-s
                for j in range(s+1):
                    for ell in range(t+1):
                        for alpha,beta in product((0,1),repeat=2):
                            m,p,q=s+k+2-alpha,k+1-alpha,j+1-alpha
                            mm,pp,qq=t+k+2-beta,k+1-beta,ell+1-beta
                            need(0 <= p <= m <= N and 0 <= q <= m, "left box domain")
                            need(0 <= pp <= mm <= N and 0 <= qq <= mm, "right box domain")
                            left=encoded_F(m,p,q,N)
                            right=encoded_F(mm,pp,qq,N)
                            need(left == F(m)[p][q] and right == F(mm)[pp][qq], "encoded E equality")
                            total += (-1)**(alpha+beta)*left*right
                            expanded_products += 1
        need(total == spine(n), "23-index expansion")
        rows.append([n,total])
    return {"generalized_pascal_cases":primitive_cases,"arbitrary_D_integer_cases":arbitrary_D_cases,
            "strip_indicator_cases":strip_cases,"master_index_count":23,
            "maximum_signed_primitive_products":4*6**4,
            "evaluated_alpha_beta_products":expanded_products,"coefficients":rows,
            "scope":"Delta-pruned and factored exact box algebra; never a full 23-dimensional Cartesian enumeration"}


def finite_diagnostics(max_shape=37,max_matrix=12):
    shape_count=0
    schur_count=0
    # Rational Gaussian envelopes: e^(-x) >= 1-x for x >= 0.
    # We report maxima on a FINITE domain with c=1/100; x<1 here.
    tail_envelope=Fraction(0)
    tail_cases=0
    for r in range(max_shape+1):
        A=F(r)[0][0]
        data=[]
        for mu in partitions(r):
            f=dimension(mu)
            need(f == corner_dimension(mu) == D(mu), "three independent dimensions")
            M3=max(abs(3*x-r) for x in mu)
            data.append((M3,f*f))
            shape_count+=1
        for threshold in sorted({0}|{v for v,_ in data}):
            x=Fraction(threshold*threshold,900*(r+1))
            need(0 <= x < 1, "tail finite rational envelope domain")
            tail=sum(weight for v,weight in data if v >= threshold)
            tail_envelope=max(tail_envelope,Fraction(tail,A)/(1-x))
            tail_cases+=1
        for p in range(r+1):
            need(F(r)[p][p] <= comb(p+2,2)**2*F(r-p)[0][0], "exact diagonal Schur bound")
            schur_count+=1
    common_pairs=0
    incidence_entries=0
    cell_tests=0
    mismatch_squared=Fraction(0)
    triangular_envelope=Fraction(0)
    matrix_cases=0
    triangle_cases=0
    for m in range(max_matrix+1):
        outers=partitions(m)
        inner_all=tuple(mu for r in range(m+1) for mu in partitions(r))
        cols={}
        independent=[[0]*(m+1) for _ in range(m+1)]
        for lam in outers:
            neighbors=[]
            weights=[0]*(m+1)
            degree=[0]*(m+1)
            for mu in inner_all:
                cell_tests+=1
                cell=horizontal_cells(lam,mu)
                need(cell == interlaces(lam,mu), "cells versus interlacing")
                if cell:
                    p=m-sum(mu)
                    weights[p]+=corner_dimension(mu)
                    degree[p]+=1
                    cols[p,mu]=cols.get((p,mu),0)+1
                    neighbors.append(mu)
                    incidence_entries+=1
            for p in range(m+1):
                need(degree[p] <= comb(p+2,2), "row Schur degree")
                for q in range(m+1):
                    independent[p][q]+=weights[p]*weights[q]
            for mu in neighbors:
                r=sum(mu)
                M3=max(abs(3*v-r) for v in mu)
                for nu in neighbors:
                    u=sum(nu)
                    N3=max(abs(3*v-u) for v in nu)
                    gap=abs(r-u)
                    need(gap <= M3+N3, "interlacing mismatch geometry")
                    need(2*M3 >= gap or 2*N3 >= gap, "tail support union")
                    common_pairs+=1
        for (p,mu),degree in cols.items():
            need(degree <= comb(p+2,2), "column Schur degree")
        need(tuple(map(tuple,independent)) == F(m), "independent cell/corner F matrix")
        for p in range(m+1):
            for q in range(m+1):
                x=Fraction((p-q)**2,100*(m+1))
                need(x < 1, "mismatch finite rational envelope domain")
                Bprod=comb(p+2,2)*comb(q+2,2)
                denominator=Bprod**2*F(m-p)[0][0]*F(m-q)[0][0]
                ratio=Fraction(F(m)[p][q]**2,denominator)/(1-x)**2
                mismatch_squared=max(mismatch_squared,ratio)
                matrix_cases+=1
                if p+q <= m:
                    ratio=Fraction(F(m)[p][q]*3**(p+q),F(m)[0][0]*Bprod)/(1-x)
                    triangular_envelope=max(triangular_envelope,ratio)
                    triangle_cases+=1
    for k in range(max_shape-1):
        dk=Fraction(comb(k+2,2),3**k)
        dn=Fraction(comb(k+3,2),3**(k+1))
        gamma=Fraction(27*(5*k+24)*(k+2),8*3**k)
        need(81*dn*Fraction(19,8)-9*dk*Fraction(27,8) == gamma > 0,"gamma algebra")
    return {"max_shape_size":max_shape,"max_incidence_size":max_matrix,
            "dimension_shapes":shape_count,"cell_strip_tests":cell_tests,
            "incidence_entries":incidence_entries,"common_outer_inner_pairs":common_pairs,
            "exact_diagonal_schur_cases":schur_count,"tail_threshold_cases":tail_cases,
            "mismatch_matrix_cases":matrix_cases,"triangle_cases":triangle_cases,
            "finite_gaussian_c":"1/100","tail_K_rational_envelope":str(tail_envelope),
            "mismatch_K_squared_rational_envelope":str(mismatch_squared),
            "triangle_K_rational_envelope":str(triangular_envelope),
            "scope":"Finite diagnostics only. No uniform all-size Gaussian constants, limiting interchange, or infinite-tail estimate is certified by this computation"}


def ct_exponent_checks():
    """Finite exponent-ledger audit of the optional 40-variable rational period.

H,T,U and SX,SY are formal labels for c(v) and sums, not additional CT
variables. No multivariate Laurent series or contour integral is expanded.
"""
    block=(
        {"z":1,"H":1,"A":-1,"B":-1,"C":-1},
        {"C":1,"H":-1},
        {"A":1,"T1":1,"U1":1},
        {"A":1,"T3":1,"U3":1,"T2":-1,"U2":-1},
        {"A":1,"T5":1,"U5":1,"T4":-1,"U4":-1},
        {"B":1,"SX":1,"T2":1,"X1":-1,"T1":-1},
        {"B":1,"SX":1,"T4":1,"X2":-1,"T3":-1},
        {"B":1,"SX":1,"X3":-1,"T5":-1},
        {"C":1,"SY":1,"U2":1,"Y1":-1,"U1":-1},
        {"C":1,"SY":1,"U4":1,"Y2":-1,"U3":-1},
        {"C":1,"SY":1,"Y3":-1,"U5":-1})
    need(len(block)==11,"CT geometric factors per block")
    variables=("A","B","C","b",*("p"+str(i) for i in range(1,6)),
               *("q"+str(i) for i in range(1,6)),"X1","X2","X3","Y1","Y2","Y3")
    need(len(set(variables)|{v+"prime" for v in variables})==40,"CT variable count")
    def ledger(indices,alpha,beta):
        k,s,t,j,ell,*coordinates=indices
        result={"z":4}
        def add(name,value):
            result[name]=result.get(name,0)+value
        for pref,outer,small,coords,choice in (("",s,j,coordinates[:9],alpha),("prime",t,ell,coordinates[9:],beta)):
            for name,e in {"A":-2+choice,"B":-1,"C":-1,"X1":-2,"X2":-1,"Y1":-2,"Y2":-1}.items():
                add(pref+name,e)
            for power,weight in zip((outer,small,*coords),block):
                for name,e in weight.items():
                    add("z" if name=="z" else pref+name,power*e)
        for name,e in {"z":1,"A":-1,"C":-1,"primeA":-1,"primeC":-1}.items():
            add(name,k*e)
        return {key:value for key,value in result.items() if value}
    def expected(indices,alpha,beta):
        k,s,t,j,ell,*coordinates=indices
        result={"z":4+s+t+k}
        for pref,outer,small,coords,choice in (("",s,j,coordinates[:9],alpha),("prime",t,ell,coordinates[9:],beta)):
            lam,mu,nu=coords[:3],coords[3:6],coords[6:]
            m=outer+k+2-choice
            p=k+1-choice
            q=small+1-choice
            values={"A":sum(lam)-m,"B":sum(mu)-m+p,"C":sum(nu)-m+q,
                    "H":outer-small,"SX":sum(mu),"SY":sum(nu)}
            for prefix,inner in (("T",mu),("U",nu)):
                exponents=(lam[0]-inner[0],inner[0]-lam[1],lam[1]-inner[1],inner[1]-lam[2],lam[2]-inner[2])
                values.update({prefix+str(i+1):v for i,v in enumerate(exponents)})
            for prefix,inner in (("X",mu),("Y",nu)):
                values.update({prefix+str(i+1):-inner[i]-(2,1,0)[i] for i in range(3)})
            result.update({pref+key:value for key,value in values.items()})
        return {key:value for key,value in result.items() if value}
    samples=[(0,)*23,(1,)*23,(5,)*23]
    for i in range(23):
        sample=[0]*23; sample[i]=1; samples.append(tuple(sample))
    for outer in product(range(3),repeat=5):
        samples.append(tuple(outer)+tuple((sum(outer)+3*i+i*i)%6 for i in range(18)))
    state=136
    for _ in range(1024):
        sample=[]
        for i in range(23):
            state=(1664525*state+1013904223)%(2**32)
            sample.append((state>>16)%6)
        samples.append(tuple(sample))
    cases=0
    for sample in samples:
        for alpha,beta in product((0,1),repeat=2):
            need(ledger(sample,alpha,beta)==expected(sample,alpha,beta),"CT exponent ledger versus Q")
            cases+=1
    # Direct polynomial expansion of the three Vandermonde factors, followed
    # by ordinary multinomial extraction, independently tests the dimension CT.
    vandermonde={(0,0,0):1}
    for i,j in ((0,1),(0,2),(1,2)):
        update={}
        for exponent,coefficient in vandermonde.items():
            for index,sign in ((i,1),(j,-1)):
                e=list(exponent); e[index]+=1; e=tuple(e)
                update[e]=update.get(e,0)+sign*coefficient
        vandermonde={e:c for e,c in update.items() if c}
    need(len(vandermonde)==6,"Vandermonde six monomials")
    dimension_cases=0
    for m in range(13):
        for mu in partitions(m):
            target=tuple(mu[i]+(2,1,0)[i] for i in range(3))
            value=0
            for e,c in vandermonde.items():
                power=tuple(target[i]-e[i] for i in range(3))
                if min(power)>=0:
                    need(sum(power)==m,"CT multinomial degree")
                    value+=c*comb(m,power[0])*comb(m-power[0],power[1])
            need(value==dimension(mu),"CT dimension coefficient")
            dimension_cases+=1
    # CT c(v)^d = B(d,d) is exactly the boundary/strip step primitive.
    for d in range(-20,21):
        need(B(d,d)==int(d>=0),"CT boundary indicator")
    return {"ct_variables":40,"geometric_factors":23,"factors_per_block":11,
            "sample_index_tuples":len(samples),"alpha_beta_ledger_checks":cases,
            "vandermonde_coefficient_shapes_through_12":dimension_cases,
            "boundary_indicator_exponents_checked":41,
            "scope":"Finite integer exponent-ledger and coefficient checks only; no full Laurent expansion, contour integration, or explicit rational diagonal is computed"}


def profile_constant_checks():
    """Exact rational prefactors only; no limit or improper integral is tested.

Using the report's symbolic identities C0=(81/16)*sqrt(3)/pi and
integral_0^infinity u^4 exp(-u^2/2) du=(3/2)*sqrt(2*pi), the common
radical in D is sqrt(6/pi). Only the remaining rational algebra is checked.
"""
    a=Fraction(27,8)*5
    D_prefactor=Fraction(81,16)*a*a*Fraction(3,2)
    tail_prefactor=Fraction(4,9**4)*D_prefactor
    need(a==Fraction(135,8),"profile gamma leading prefactor")
    need(D_prefactor==Fraction(4428675,2048),"profile D rational prefactor")
    need(tail_prefactor==Fraction(675,512),"profile amplitude tail rational prefactor")
    return {"a":str(a),"D_sqrt_6_over_pi_prefactor":str(D_prefactor),
            "four_D_over_9_pow_4_sqrt_6_over_pi_prefactor":str(tail_prefactor),
            "scope":"Exact rational coefficient algebra only; no profile limit, cancellation limit, improper integral, or infinite tail is computationally certified"}
