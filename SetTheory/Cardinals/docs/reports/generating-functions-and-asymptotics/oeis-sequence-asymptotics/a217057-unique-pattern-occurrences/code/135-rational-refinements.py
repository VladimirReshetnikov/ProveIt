"""Exact finite arithmetic and explicitly limited diagnostics for Report 135.

Standard library only. No filesystem writes or local imports. The verifier loads
this module and the unchanged Report134 modules from verified in-memory bytes.
Finite checks complement the article's proofs; none proves an asymptotic limit.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from functools import lru_cache
from itertools import permutations
from math import comb, factorial


def require(condition, message):
    if not condition:
        raise ValueError(message)


@lru_cache(None)
def binomial(a, b):
    """Everywhere-defined coefficient [z^b](1+z)^a, including a<0."""
    if b < 0:
        return 0
    if a >= 0:
        return comb(a, b) if b <= a else 0
    return (-1)**b * comb(b-a-1, b)


SIGNS = [(p, (-1)**sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3)))
         for p in permutations((1, 2, 3))]


@lru_cache(None)
def six_term_dimension(shape):
    m = sum(shape)
    total = 0
    for p, sign in SIGNS:
        e = [shape[i]-(i+1)+p[i] for i in range(3)]
        require(sum(e) == m, "dimension exponent sum")
        total += sign * binomial(m, e[0]) * binomial(m-e[0], e[1]) * binomial(e[2], e[2])
    return total


@lru_cache(None)
def encoded_boundary(m):
    out = [[0]*(m+1) for _ in range(m+1)]
    for a in range(m+1):
        for b in range(a+1):
            c = m-a-b
            if not (0 <= c <= b):
                continue
            values = [0]*(m+1)
            for u in range(b, a+1):
                for v in range(c, b+1):
                    for w in range(c+1):
                        values[m-u-v-w] += six_term_dimension((u,v,w))
            for p, x in enumerate(values):
                for q, y in enumerate(values):
                    out[p][q] += x*y
    return out


def encoded_counts(max_n):
    layers = {}
    for s in range(max_n-3):
        outer, inner = encoded_boundary(s+2), encoded_boundary(s+1)
        layers[s] = {(i,j): outer[i+1][j+1]-inner[i][j]
                     for i in range(s+1) for j in range(s-i+1)}
    out = []
    for n in range(max_n+1):
        total = 0
        if n >= 4:
            for s in range(n-3):
                for (i,j), h in layers[s].items():
                    for (k,l), g in layers[n-4-s].items():
                        total += h*g*binomial(i+k,i)*binomial(j+l,j)
        out.append(total)
    return out


# Polynomials in k, represented by low-to-high rational coefficient lists.
def padd(a, b):
    out = [Q(0)]*max(len(a), len(b))
    for i, c in enumerate(a): out[i] += c
    for i, c in enumerate(b): out[i] += c
    while len(out)>1 and out[-1] == 0: out.pop()
    return out


def pscale(a, c):
    return [x*c for x in a]


def pmul(a, b):
    out = [Q(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i+j] += x*y
    return padd(out, [Q(0)])


def peval(a, k):
    out = Q(0)
    for c in reversed(a): out = out*k+c
    return out


def theta_polynomials(max_j):
    """All-k exact identity theta^j(1-x)^(-k-1) at x=1/3.

    Result is divided by (3/2)^k. Use theta^j=sum_r S(j,r)x^r D^r,
    so its r-th term is (3/2) S(j,r)(k+1)_r/2^r.
    """
    stirling = [[1]]
    for j in range(1, max_j+1):
        row = [0]*(j+1)
        for r in range(1,j+1):
            row[r] = (stirling[-1][r-1] +
                      (r*stirling[-1][r] if r<len(stirling[-1]) else 0))
        stirling.append(row)
    rising = [[Q(1)]]
    for r in range(1,max_j+1): rising.append(pmul(rising[-1],[Q(r),Q(1)]))
    out = []
    for j in range(max_j+1):
        poly = [Q(0)]
        for r in range(j+1):
            poly = padd(poly, pscale(rising[r], Q(3,2)*Q(stirling[j][r],2**r)))
        out.append(poly)
    return out


def transform_polynomials():
    moments = theta_polynomials(4)
    operators = {'D': [Q(1),Q(3,2),Q(1,2)],
                 'E': [Q(1),Q(5,6),Q(1,6)],
                 'J': [Q(0),Q(-1,2),Q(-1,4),Q(1,2),Q(1,4)],
                 'K': [Q(0),Q(1,2),Q(11,12),Q(1,2),Q(1,12)]}
    derived = {}
    for name, operator in operators.items():
        value = [Q(0)]
        for degree, c in enumerate(operator): value = padd(value,pscale(moments[degree],c))
        derived[name] = value
    displayed = {'D': pscale([18,11,1],Q(3,16)),
                 'E': pscale([38,15,1],Q(1,16)),
                 'J': pscale(pmul(pmul([1,1],[2,1]),[108,23,1]),Q(3,128)),
                 'K': pscale(pmul([1,1],[648,290,33,1]),Q(1,128))}
    require(derived == displayed, "all-k D/E/J/K polynomial identity")
    return derived


def transforms(k):
    scale = Q(3,2)**k
    return (Q(3,16)*(k*k+11*k+18)*scale,
            Q(1,16)*(k*k+15*k+38)*scale,
            Q(3,128)*(k+1)*(k+2)*(k*k+23*k+108)*scale,
            Q(1,128)*(k+1)*(k**3+33*k*k+290*k+648)*scale)


def finite_partials(primary, max_t=20):
    r = s = Q(0)
    out = []
    for t in range(max_t+1):
        rt = st = Q(0)
        for (k,l), h in primary.halves(t).items():
            d,e,j,v = transforms(k)
            D,E,J,V = transforms(l)
            rt += h*(e*E-d*D/9)
            st += h*((4*t+8)*e*E-v*E-e*V-
                     ((4*t+12)*d*D-j*D-d*J)/9)
        rt *= Q(2,81*9**t)
        st *= Q(2,81*9**t)
        r += rt; s += st
        out.append({'t':t, 'R_term':str(rt), 'S_term':str(st),
                    'R_partial':str(r), 'S_partial':str(s),
                    'beta_partial_not_certified':str(s/r-Q(11,2))})
    return out


def check_ct_exponents():
    # The dictionaries transcribe the twelve displayed rational weights.
    weights = [dict(z=1,H=1,A=-1,B=-1,C=-1),dict(B=1,P=1,H=-1),dict(C=1,Q=1,H=-1),
        dict(A=1,T1=1,V1=1),dict(A=1,T3=1,V3=1,T2=-1,V2=-1),
        dict(A=1,T5=1,V5=1,T4=-1,V4=-1),
        dict(B=1,U1=1,T2=1,T1=-1),dict(B=1,U2=1,T4=1,T3=-1),dict(B=1,U3=1,T5=-1),
        dict(C=1,W1=1,V2=1,V1=-1),dict(C=1,W2=1,V4=1,V3=-1),dict(C=1,W3=1,V5=-1)]
    def expected(indices):
        s,i,j=indices[:3]; lam=indices[3:6]; mu=indices[6:9]; nu=indices[9:12]
        result=dict(z=s,H=s-i-j,A=sum(lam)-s,B=sum(mu)-s+i,C=sum(nu)-s+j,P=i,Q=j)
        for prefix, vec in [('U',mu),('W',nu)]:
            for r,value in enumerate(vec,1): result[prefix+str(r)]=value
        for prefix,vec in [('T',mu),('V',nu)]:
            gaps=(lam[0]-vec[0],vec[0]-lam[1],lam[1]-vec[1],vec[1]-lam[2],lam[2]-vec[2])
            for r,value in enumerate(gaps,1): result[prefix+str(r)]=value
        return {k:v for k,v in result.items() if v}
    for column in range(12):
        vector=[0]*12;vector[column]=1
        require(weights[column] == expected(vector),"CT exponent column "+str(column))
    # (1-A)/(A^2 B C) has exactly these two signed monomials.
    numerator={( -2,-1,-1):1,(-1,-1,-1):-1}
    require(numerator == {(-2+alpha,-1,-1):(-1)**alpha for alpha in (0,1)},"H numerator")
    for s in range(9):
        for i in range(s+1):
            for alpha in (0,1):
                m,p=s+2-alpha,i+1-alpha
                require(m-p==s+1-i,"H alpha-independent inner size")
    # Exact radii bounds (z chosen strictly below epsilon^3/6 in the proof).
    epsilon=Q(1,100)
    require(9*epsilon<1 and 3*epsilon<1,"CT non-z weights uniformly below one")
    for i in range(13):
        for k in range(13):
            product=[0]*(i+k+1)
            for a in range(i+1):
                for b in range(k+1): product[a+b]+=comb(i,a)*comb(k,b)
            require(product[i]==comb(i+k,i),"shuffle coefficient")
    return {'independent_exponent_columns':12,'geometric_denominator_factors':24,
            'constant_term_variables':42,'shuffle_pairs':169,
            'scope':'Exact exponents, numerator, radii inequalities, and finite shuffle coefficients; no numerical 42-dimensional integration'}


# Tiny exact polynomial ring in the formal symbols s, beta, lambda.
def add(a,b):
    c=dict(a)
    for k,v in b.items(): c[k]=c.get(k,Q(0))+v
    return {k:v for k,v in c.items() if v}


def mul(a,b):
    c={}
    for k,x in a.items():
        for l,y in b.items():
            n=tuple(u+v for u,v in zip(k,l));c[n]=c.get(n,Q(0))+x*y
    return {k:v for k,v in c.items() if v}


def scale(a,x): return {k:v*x for k,v in a.items() if v*x}


def check_inverse_formal():
    s={(1,0,0):Q(1)}; b={(0,1,0):Q(1)}; lam={(0,0,1):Q(1)}
    bl=mul(b,lam); ss=mul(s,s)
    t=add(scale(s,4),scale(bl,-1))
    v=add(add(scale(s,16),scale(bl,-4)),add(scale(ss,-2),mul(bl,s)))
    # Substitute Y=L+s+t/L+v/L^2 into lambda*y-4log(y)+log(M0)+beta/y-L.
    c1=add(add(t,scale(s,-4)),bl)
    c2=add(add(v,scale(t,-4)),add(scale(ss,2),scale(mul(bl,s),-1)))
    require(not c1 and not c2,"inverse formal 1/L and 1/L^2 cancellation")
    c3=add(add(scale(v,-4),scale(mul(s,t),4)),
           add(scale(mul(ss,s),Q(-4,3)),mul(bl,add(ss,scale(t,-1)))))
    require(max(k[0] for k in c3)==3,"inverse next residual is cubic in s")
    return {'coefficients_1_over_L_and_1_over_L2':'zero identically',
            'next_residual_polynomial':[{ 'powers_s_beta_lambda':list(k),'coefficient':str(v)} for k,v in sorted(c3.items())],
            'scope':'Formal corrected continuous model only; actual count inverse retains O(L^-2) uncertainty inside ceilings'}


def check_local_coefficients():
    """Exact centered-angle Taylor identities in the polynomial ring Q[x,y]."""
    x={(1,0):Q(1)};y={(0,1):Q(1)}
    theta=(x,y,scale(add(x,y),-1))
    q={};squares={};fourths={}
    for a in theta:q=add(q,mul(a,a))
    for i in range(3):
        for j in range(i+1,3):
            gap=add(theta[i],scale(theta[j],-1))
            square=mul(gap,gap)
            squares=add(squares,square);fourths=add(fourths,mul(square,square))
    require(squares==scale(q,3), "centered quadratic gap identity")
    require(scale(fourths,Q(1,108))==scale(mul(q,q),Q(1,24)),
            "trace norm fourth-order identity")
    trace_quadratic=scale(q,Q(-1,3))
    trace_quartic=scale(mul(q,q),Q(1,24))
    logarithm_quartic=add(trace_quartic,scale(mul(trace_quadratic,trace_quadratic),Q(-1,2)))
    require(logarithm_quartic==scale(mul(q,q),Q(-1,72)),"trace logarithm fourth-order coefficient")
    require(scale(squares,Q(-1,12))==scale(q,Q(-1,4)),"Weyl density quadratic coefficient")
    moments=[Q(3**r*factorial(3+r),factorial(3)) for r in (1,2)]
    require(moments==[Q(12),Q(180)],"Gamma radial moments")
    coefficient=-moments[0]/4-moments[1]/72
    require(coefficient==Q(-11,2),"avoidance first correction coefficient")
    return {'centered_trace_and_Weyl_polynomial_identities':'PASS',
            'radial_moments':[str(v) for v in moments],
            'avoidance_first_coefficient':str(coefficient),
            'scope':'Exact local Taylor coefficients and radial moments; analytic tail and uniform remainder estimates are proved in the article'}


def inverse_numeric():
    """Synthetic M0=1, beta=2. This does not approximate unknown R,S,beta."""
    rows=[]
    with localcontext() as ctx:
        ctx.prec=80
        lam=Decimal(9).ln();beta=Decimal(2)
        for L in map(Decimal,('100','1000','10000')):
            s=4*L.ln()-4*lam.ln() # log M0=0
            t=4*s-beta*lam
            v=16*s-4*beta*lam-2*s*s+beta*lam*s
            x1=(L+s+t/L)/lam;x2=x1+v/(lam*L*L)
            y=x2
            for _ in range(16):
                f=lam*y-4*y.ln()+beta/y-L
                y -= f/(lam-4/y-beta/(y*y))
            residual=lam*y-4*y.ln()+beta/y-L
            require(abs(residual)<Decimal('1e-65'),"synthetic Newton residual")
            rows.append({'L':str(L),'model_M0':'1','model_beta':'2',
                         'x1_error':format(y-x1,'.24E'), 'x2_error':format(y-x2,'.24E'),
                         'x2_error_scaled_L3_over_logL3':format((y-x2)*L**3/L.ln()**3,'.24E'),
                         'root_residual_abs':format(abs(residual),'.5E')})
    return {'scope':'Numerical sanity check of synthetic continuous model; no threshold or amplitude certification', 'rows':rows}


def fixed_boundary_counts(n, boundaries=(0,1,2,3,4)):
    """Independent short-strip calculation, exact integer arithmetic."""
    fac=[factorial(i) for i in range(n+3)]
    def dimension(a,b,c):
        num=fac[a+b+c]*(a-b+1)*(a-c+2)*(b-c+1)
        den=fac[a+2]*fac[b+1]*fac[c]
        value,remainder=divmod(num,den)
        require(not remainder,"fixed-boundary hook integrality")
        return value
    compositions={p:[(x,y,p-x-y) for x in range(p+1) for y in range(p-x+1)] for p in boundaries}
    A=0;F={(p,q):0 for p in boundaries for q in boundaries}
    for c in range(n//3+1):
        for b in range(c,(n-c)//2+1):
            a=n-b-c;f=dimension(a,b,c);A+=f*f;V={}
            for p in boundaries:
                V[p]=sum(dimension(a-x,b-y,c-z) for x,y,z in compositions[p]
                         if a-x>=b and b-y>=c and c>=z)
            for p in boundaries:
                for q in boundaries:F[p,q]+=V[p]*V[q]
    return A,F


def boundary_diagnostics():
    out=[]
    for n in (30,60,120,240):
        A,F=fixed_boundary_counts(n)
        for p in (0,1):
            for q in (0,1):require(F[p,q]==A,"h0/h1 exact identity")
        for p,q in ((0,2),(2,2),(2,3),(3,4)):
            d=Q(comb(p+2,2)*comb(q+2,2),3**(p+q))
            error=Q(F[p,q],A)/d-1
            first=-Q(p*(p-1)+q*(q-1),2)
            out.append({'n':n,'p':p,'q':q,'scaled_first':str(n*error),
                        'target_first':str(first),'scaled_second_residual':str(n*n*(error-first/n))})
    return {'scope':'Finite exact residuals illustrate the fixed-boundary expansion; they do not verify uniform remainders or asymptotic convergence','rows':out}


def replay(primary, independent, fixture):
    require(binomial(-3,4)==15 and binomial(-3,3)==-10 and binomial(2,3)==0,
            "generalized negative upper arguments")
    require([binomial(r,r) for r in range(-8,9)]==[0]*8+[1]*9,"step indicator")
    require([binomial(0,r) for r in range(-8,9)]==[0]*8+[1]+[0]*8,"delta indicator")
    shapes=0
    for m in range(61):
        for shape in primary.partitions3(m):
            value=six_term_dimension(shape)
            require(value==primary.dimension(shape)==independent.recursive_dimension(shape),"three dimension constructions")
            shapes+=1
    entries=0
    for m in range(21):
        require(encoded_boundary(m)==primary.boundary(m),"encoded F matrix "+str(m))
        entries+=(m+1)**2
    matrices,_=independent.boundary_layers(12)
    for m,matrix in enumerate(matrices):require(matrix==encoded_boundary(m),"independent cell-strip F matrix")
    values=encoded_counts(20)
    require(values==fixture['u_0_through_20'],"exact u fixture")
    require(values==[primary.exact_count(n) for n in range(21)],"hook and binomial u")
    transforms_exact=transform_polynomials()
    require(transforms(0)==(Q(27,8),Q(19,8),Q(81,16),Q(81,16)),"transform normalization")
    partials=finite_partials(primary,20)
    for t in fixture['partial_indices']:
        require(partials[t]==fixture['finite_partials'][str(t)],"exact R/S partial fixture")
    old_r,old_terms=primary.positive_series([primary.halves(t) for t in range(21)])
    require(str(old_r)==partials[-1]['R_partial'],"old/new R transforms")
    require([str(x) for x in old_terms]==[x['R_term'] for x in partials],"R layers")
    return {'status':'PASS', 'tableau_dimensions':shapes,'dimension_size_range':[0,60],
            'binomial_F_entries':entries,'binomial_F_size_range':[0,20],
            'independent_cell_strip_F_size_range':[0,12], 'u_0_through_20':values,
            'transform_polynomials_after_dividing_by_3_over_2_to_k':{k:[str(v) for v in p] for k,p in transforms_exact.items()},
            'ct':check_ct_exponents(),'local_coefficients':check_local_coefficients(),'inverse_formal':check_inverse_formal(),
            'inverse_numeric':inverse_numeric(),'fixed_boundary_diagnostics':boundary_diagnostics(),
            'partial_sum_scope':'R partials are lower bounds; S and beta partials are not certified estimates or bounds of their limits',
            'finite_partials':partials,
            'proof_scope':'Finite and algebraic checks do not prove combinatorial identities, D-finiteness, asymptotics, tail bounds, or inverse-threshold enclosures. See Reports 134 and 135.'}
