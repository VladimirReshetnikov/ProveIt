"""Exact algebra and finite diagnostics for Report135's second correction and logarithm.

Standard library only. No files are read or written. Pass the verified first
refinement module and exact tableau module to run(). Finite checks are not an
analytic proof; the required uniform estimates are supplied in Report135.
"""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from math import comb, factorial


def require(ok, message):
    if not ok: raise ValueError(message)


def a(p):return Q(p*(p-1),2)
def b(p):return Q(p*(p-1)*(2*p*p-6*p+5),16)
def boundary_b(p,q):return b(p)+b(q)+Q(5,4)*a(p)*a(q)


def new_transforms(first):
    # Exact polynomials in i to which the binomial Euler moments are applied.
    c=[Q(1),Q(3,2),Q(1,2)]
    e=[Q(1),Q(5,6),Q(1,6)]
    bp=first.pscale(first.pmul(first.pmul([0,1],[-1,1]),[5,-6,2]),Q(1,16))
    bp1=first.pscale(first.pmul(first.pmul([0,1],[1,1]),[1,-2,2]),Q(1,16))
    moments=first.theta_polynomials(6)
    actual={}
    for name,poly in [('L',first.pmul(c,bp)),('M',first.pmul(e,bp1))]:
        out=[Q(0)]
        for j,coefficient in enumerate(poly):out=first.padd(out,first.pscale(moments[j],coefficient))
        actual[name]=out
    expected={
      'L':first.pscale(first.pmul(first.pmul([1,1],[2,1]),[5616,3424,657,46,1]),Q(3,2048)),
      'M':first.pscale(first.pmul([1,1],[33696,31784,9726,1197,60,1]),Q(1,2048))}
    require(actual==expected,'all-k L/M polynomial transforms')
    return actual


def contraction():
    # theta^j=sum_r S(j,r)x^r D^r. At x=y=1/3,
    # x^r y^s D_x^r D_y^s(1-x-y)^-1 = 3(r+s)! exactly.
    stirling=((1,),(0,1),(0,1,1))
    def moment(j,k):
        return sum(Q(3*sj*sk*factorial(r+s)) for r,sj in enumerate(stirling[j])
                   for s,sk in enumerate(stirling[k]))
    def pair(left,right):
        return sum(c*d*moment(j,k) for j,c in enumerate(left) for k,d in enumerate(right))
    d=(Q(1),Q(3,2),Q(1,2));e=(Q(1),Q(5,6),Q(1,6))
    values={name:pair(x,y) for name,x,y in [('dd',d,d),('de',d,e),('ee',e,e)]}
    require(values=={'dd':Q(99),'de':Q(49),'ee':Q(25)},'bivariate contractions')
    cc=81**2*values['ee']**2-2*81*9*values['de']**2+9**2*values['dd']**2
    require(cc==1393848,'C contraction')
    kappa=Q(40*81,16*9**4)*cc
    require(kappa==43020,'positive logarithm prefactor')
    return {'one_coordinate':{k:str(v) for k,v in values.items()},'C_C':str(cc),
            'kappa_factor_of_sqrt3_over_pi':str(kappa)}


def local_coefficients(first):
    add,mul,scale=first.add,first.mul,first.scale
    def power(a,n):
        out={(0,0):Q(1)}
        for _ in range(n):out=mul(out,a)
        return out
    x={(1,0):Q(1)};y={(0,1):Q(1)};theta=(x,y,scale(add(x,y),-1))
    q={};t={};sums={p:{} for p in (2,4,6)};discriminant={(0,0):Q(1)}
    gap_squares=[]
    for v in theta:q=add(q,power(v,2));t=add(t,power(v,3))
    for i in range(3):
        for j in range(i+1,3):
            gap=add(theta[i],scale(theta[j],-1));gap_squares.append(power(gap,2))
            discriminant=mul(discriminant,power(gap,2))
            for p in sums:sums[p]=add(sums[p],power(gap,p))
    require(sums[2]==scale(q,3),'quadratic angle identity')
    require(sums[4]==scale(power(q,2),Q(9,2)),'quartic angle identity')
    require(sums[6]==add(scale(power(q,3),Q(33,4)),scale(power(t,2),-9)),'sextic angle identity')
    require(discriminant==add(scale(power(q,3),Q(1,2)),scale(power(t,2),-3)),'discriminant identity')
    norm1=scale(sums[2],Q(-1,9));norm2=scale(sums[4],Q(1,108));norm3=scale(sums[6],Q(-1,3240))
    log3=add(add(norm3,scale(mul(norm1,norm2),-1)),scale(power(norm1,3),Q(1,3)))
    require(log3==add(scale(power(q,3),Q(-13,12960)),scale(power(t,2),Q(1,360))),'trace log sixth')
    density4=scale(sums[4],Q(1,360))
    for i in range(3):
        for j in range(i+1,3):density4=add(density4,scale(mul(gap_squares[i],gap_squares[j]),Q(1,144)))
    require(density4==scale(power(q,2),Q(9,320)),'factored Weyl quartic')
    qm={j:Q(3**j*factorial(j+3),factorial(3)) for j in range(5)}
    # Angular average of cos^2(3phi) against sin^2(3phi) is 1/4.
    # Integral sin^2 cos^2 /(integral sin^2) = (1/8)/(1/2).
    angular=Q(1,8)/Q(1,2)
    tm=qm[3]*angular/6
    alpha=-qm[1]/4-qm[2]/72
    gamma=Q(9,320)*qm[2]+qm[3]/405+tm/360+qm[4]/10368
    cov=-(qm[2]-qm[1]**2)/4-(qm[3]-qm[1]*qm[2])/72
    require(alpha==Q(-11,2) and gamma==20 and cov==-24 and tm==135,'second local integral coefficients')
    # Rational polynomial equalities in the boundary index p.
    pmul,pscale,padd=first.pmul,first.pscale,first.padd
    ap=pscale(pmul([0,1],[-1,1]),Q(1,2))
    vp=pscale(pmul(pmul([0,1],[-1,1]),[-11,-6,2]),Q(1,2880))
    bp=pscale(pmul(pmul([0,1],[-1,1]),[5,-6,2]),Q(1,16))
    require(padd(pscale(ap,2),pscale(vp,180))==bp,'all-p boundary second coefficient')
    m4=pscale(pmul(pmul([0,1],[3,1]),[-3,6,2]),Q(1,30))
    quartic=padd(pscale(m4,Q(1,96)),
                  padd(pscale(pmul([0,1],[1,2]),Q(1,144)),
                       pscale(pmul([0,0,1],[3,1]),Q(-1,144))))
    require(quartic==vp,'all-p normalized character quartic')
    checks=0
    for p in range(31):
        compositions=[(i,j,p-i-j) for i in range(p+1) for j in range(p-i+1)]
        avg=Q(sum((i-j)**4 for i,j,_ in compositions),len(compositions))
        require(avg==first.peval(m4,p),'composition fourth moment')
        checks+=1
    return {'radial_moments':{str(k):str(v) for k,v in qm.items()},'T2_moment':str(tm),
            'avoidance_first':str(alpha),'avoidance_second':str(gamma),'Q_moment_correction':str(cov),
            'composition_fourth_moments_checked':checks,'all_p_boundary_polynomials':'PASS'}


def shift_and_endpoint(first):
    # Sparse polynomials in (h,a,b,z,C,B,D), with series in e=1/n.
    add,mul,scale=first.add,first.mul,first.scale
    zero=(0,)*7;one={zero:Q(1)}
    def var(i):
        key=list(zero);key[i]=1;return {tuple(key):Q(1)}
    h,a,b,z,C,B,D=map(var,range(7))
    def power(p,n):
        r=one
        for _ in range(n):r=mul(r,p)
        return r
    def product(*series):
        out=[one,{},{},{}]
        for f in series:
            new=[{},{},{},{}]
            for i,x in enumerate(out):
                for j,y in enumerate(f):
                    if i+j<4:new[i+j]=add(new[i+j],mul(x,y))
            out=new
        return out
    alpha=Q(-11,2);gamma=Q(20)
    shift=product([one,scale(h,-4),scale(power(h,2),10)],
                  [one,scale(one,alpha),add(scale(one,gamma),scale(h,-alpha))],
                  [one,scale(a,-1),add(b,mul(a,h))],
                  [one,scale(one,-alpha),scale(one,alpha*alpha-gamma)])
    require(shift[1]==add(scale(h,-4),scale(a,-1)),'shift first')
    expected=add(add(scale(power(h,2),10),scale(h,-alpha)),add(scale(mul(h,a),5),b))
    require(shift[2]==expected,'shift second')
    endpoint=product([one,scale(z,4),scale(power(z,2),10),scale(power(z,3),20)],
      [one,scale(one,alpha),add(scale(one,gamma),scale(z,alpha)),add(scale(power(z,2),alpha),scale(z,2*gamma))],
      [one,scale(one,-alpha),scale(one,alpha*alpha-gamma),scale(one,2*alpha*gamma-alpha**3)],
      [C,B,add(D,mul(B,z)),add(mul(B,power(z,2)),scale(mul(D,z),2))])
    require(endpoint[1]==add(scale(mul(z,C),4),B),'endpoint first')
    require(endpoint[2]==add(mul(add(scale(power(z,2),10),scale(z,alpha)),C),add(scale(mul(z,B),5),D)),'endpoint second')
    third=add(endpoint[3],scale(mul(power(z,3),C),-20))
    require(all(key[3]<=2 for key in third),'only cubic endpoint term is 20 z^3 C')
    # Remaining finite-boundary S2 polynomial factors, identities for all t.
    padd,pmul,pscale=first.padd,first.pmul,first.pscale
    tz=[Q(4),Q(1)]
    ee=padd(padd(pscale(pmul(tz,tz),10),pscale(tz,alpha-40)),[Q(51)])
    dd=padd(padd(pscale(pmul(tz,tz),10),pscale(tz,alpha-20)),[Q(31,2)])
    require(ee==[Q(29),Q(69,2),Q(10)] and dd==[Q(147,2),Q(109,2),Q(10)],'S2 EE and DD factors')
    require(padd(pscale(tz,-5),[Q(10)])==[Q(-10),Q(-5)],'S2 KE factor')
    require(padd(pscale(tz,-5),[Q(5)])==[Q(-15),Q(-5)],'S2 JD factor')
    return {'shift_and_endpoint_series':'PASS','remaining_third_endpoint_degree_in_z':2,'finite_boundary_S2_factors':'PASS'}


def inverse_formal(first):
    # Independent formal symbols s,beta,lambda,mu,eta,ell; ell=log L-log lambda.
    add,mul,scale=first.add,first.mul,first.scale
    def var(i):
        a=[0]*6;a[i]=1;return {tuple(a):Q(1)}
    s,beta,lam,mu,eta,ell=map(var,range(6))
    s2=mul(s,s);s3=mul(s2,s);bl=mul(beta,lam);ml2=mul(mu,mul(lam,lam));el3=mul(eta,mul(lam,mul(lam,lam)))
    t=add(scale(s,4),scale(bl,-1))
    v=add(add(scale(t,4),scale(s2,-2)),add(mul(bl,s),scale(ml2,-1)))
    w=add(add(scale(v,4),scale(mul(s,t),-4)),
          add(scale(s3,Q(4,3)),add(scale(mul(bl,add(s2,scale(t,-1))),-1),
          add(scale(mul(ml2,s),2),scale(mul(el3,ell),-1)))))
    c1=add(add(t,scale(s,-4)),bl)
    c2=add(add(v,scale(t,-4)),add(scale(s2,2),add(scale(mul(bl,s),-1),ml2)))
    c3=add(add(w,scale(v,-4)),add(scale(mul(s,t),4),add(scale(s3,Q(-4,3)),
            add(mul(bl,add(s2,scale(t,-1))),add(scale(mul(ml2,s),-2),mul(el3,ell))))))
    require(not c1 and not c2 and not c3,'x3 inverse formal cancellation')
    return {'coefficients_1_over_L_through_1_over_L3':'zero identically',
            'scope':'Corrected continuous model only; integer inverse retains O(L^-3) uncertainty'}


def inverse_numeric():
    rows=[]
    with localcontext() as ctx:
        ctx.prec=80
        lam=Decimal(9).ln();beta=Decimal(2);mu=Decimal(3);eta=Decimal(5)
        for L in map(Decimal,('100','1000','10000')):
            s=4*L.ln()-4*lam.ln();t=4*s-beta*lam
            v=4*t-2*s*s+beta*lam*s-mu*lam*lam
            w=4*v-4*s*t+Decimal(4)/3*s**3-beta*lam*(s*s-t)+2*mu*lam*lam*s-eta*lam**3*(L.ln()-lam.ln())
            x3=(L+s+t/L+v/L**2+w/L**3)/lam;y=x3
            for _ in range(16):
                f=lam*y-4*y.ln()+beta/y+mu/y**2+eta*y.ln()/y**3-L
                derivative=lam-4/y-beta/y**2-2*mu/y**3+eta*(1-3*y.ln())/y**4
                y-=f/derivative
            residual=lam*y-4*y.ln()+beta/y+mu/y**2+eta*y.ln()/y**3-L
            require(abs(residual)<Decimal('1e-65'),'x3 synthetic Newton residual')
            rows.append({'L':str(L),'x3_error':format(y-x3,'.24E'),
                         'scaled_error_L4_over_logL4':format((y-x3)*L**4/L.ln()**4,'.24E'),
                         'root_residual_abs':format(abs(residual),'.5E')})
    return {'scope':'Synthetic M0=1,beta=2,mu=3,eta=5; no R,S,S2 or threshold approximation','rows':rows}


def finite_partials(first,primary,max_t=20):
    polys=new_transforms(first);out=[];total=Q(0)
    for t in range(max_t+1):
        term=Q(0)
        for (k,l),h in primary.halves(t).items():
            d,e,j,v=first.transforms(k);D,E,J,V=first.transforms(l)
            L=first.peval(polys['L'],k)*Q(3,2)**k;M=first.peval(polys['M'],k)*Q(3,2)**k
            LL=first.peval(polys['L'],l)*Q(3,2)**l;MM=first.peval(polys['M'],l)*Q(3,2)**l
            value=(10*t*t+Q(69,2)*t+29)*e*E-(5*t+10)*(v*E+e*V)+M*E+e*MM+Q(5,4)*v*V
            value-=((10*t*t+Q(109,2)*t+Q(147,2))*d*D-(5*t+15)*(j*D+d*J)+L*D+d*LL+Q(5,4)*j*J)/9
            term+=h*value
        term*=Q(2,81*9**t);total+=term
        out.append({'t':t,'S2_term':str(term),'S2_partial':str(total)})
    return out


def boundary_diagnostics(first):
    rows=[]
    for n in (30,60,120,240,480):
        A,F=first.fixed_boundary_counts(n)
        for p,q in ((0,2),(2,2),(2,3),(3,4)):
            d=Q(comb(p+2,2)*comb(q+2,2),3**(p+q))
            scaled=n*n*(Q(F[p,q],A)/d-1+(a(p)+a(q))/n)
            target=boundary_b(p,q)
            rows.append({'n':n,'p':p,'q':q,'scaled_second_residual':str(scaled),
                         'target':str(target),'scaled_third_residual':str(n*(scaled-target))})
    return {'scope':'Exact finite diagnostics, not uniform asymptotic remainder or convergence checks','rows':rows}


def run(first,primary):
    polys=new_transforms(first)
    return {'status':'PASS','scope':'Exact finite/algebraic checks only; analytic second-correction proof is in Report135',
            'new_transform_polynomials':{k:[str(c) for c in v] for k,v in polys.items()},
            'contraction':contraction(),'local':local_coefficients(first),
            'shift_endpoint':shift_and_endpoint(first),'inverse_formal':inverse_formal(first),
            'inverse_numeric':inverse_numeric(),'boundary_diagnostics':boundary_diagnostics(first),
            'partial_scope':'Exact finite signed S2 partials; no certified approximation or bound for S2 or delta',
            'finite_partials':finite_partials(first,primary)}
