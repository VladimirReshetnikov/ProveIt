#!/usr/bin/env python3
"""Uniform exact rational certificates and explicitly separate finite sanity tests.

Standard library only. No interpolation, recurrence fitting, network access,
source-tree writes, or disabled-with-optimization assertions are used.
The sole output is deterministic JSON on stdout.
"""
from fractions import Fraction as F
from itertools import combinations
from functools import lru_cache
from math import factorial, prod
import json
from exact_algebra import Rat, Poly, Sparse, N as n, T as t, X as x, Y as y, W as w, J as j, require, self_test
from printed_coefficients import P,Q,D,P_next_printed,Q_next_oeis,u,v,gamma,L_oeis
from asymptotic_certificate import verify as verify_asymptotics

checks=[]
def certify(label,residual):
    require(residual == 0, 'nonzero exact residual: '+label)
    checks.append(label)


def scalar_coeff(p,e): return p.terms.get(e,Rat())
def vector(p):
    allowed=[(0,1,0,0,0),(0,0,1,0,0),(0,0,0,0,0)]
    require(all(e in allowed for e in p.terms),'non-affine period expression')
    return [scalar_coeff(p,e) for e in allowed]


def uniform():
    self_test()
    lam=-(n+1)**2/(2*n*(2*n+1));mu=(n+1)**2/(2*(2*n+1))
    nu=-(n+1)**2/(3*(3*n+1)*(3*n+2))
    q=-(n+1)/(6*n*(2*n+1))+(n+1)*(5*n+3)*t/(6*n*(2*n+1)*(3*n+2))-(n+1)*t*t/(3*(3*n+1)*(3*n+2))
    r=(n+1)/(6*(2*n+1))+(7*n*n+9*n+3)*t/(6*(2*n+1)*(3*n+2))-n*n*(n+1)*t*t/(3*(2*n+1)*(3*n+1)*(3*n+2))
    qt=(1-t)*q
    yres=lam*n*n*(1-t)**2+mu*(n*(1-t)*(1+t)+t*(1-t)+(2*n+1)*t*(1+t))-(n+1)**2*t
    certify('y contiguous ODE: all t coefficients',yres)
    certify('y contiguous endpoint',2*mu-(n+1)**2/(2*n+1))
    certify('x contiguous y coefficient',-nu*t**3+t*qt.derivative(0)-3*(n+1)*qt-(2*n-1)*t*q+lam*(1-t)**2)
    certify('x contiguous t^n coefficient',t*r.derivative(0)-(2*n+3)*r+n*n*q+mu*(1+t))
    certify('x leading coefficient ratio',nu+(n+1)**3/((3*n+1)*(3*n+2)*(3*n+3)))
    # DD is t(1-t) times the derivative along the three differential equations.
    def DD(p):
        return t*(1-t)*p.derivative(0)+(1-t)*(3*n*x-y)*p.derivative(1)+(n*n*w-(2*n-1)*t*y)*p.derivative(2)+n*w*(1-t)*p.derivative(3)
    certify('general V_j integration-by-parts flux',j*w*(1-t)**2*y+DD(w*(1-t)*y)-((n+j)*w*y*(1-t)-(3*n+j)*t*(1-t)*w*y+n*n*w*w*(1-t)))
    certify('general Y_j integration-by-parts flux',j*(1-t)**2*y*y+DD((1-t)*y*y)-(j*(1-t)*y*y-(4*n+j-1)*t*(1-t)*y*y+2*n*n*w*y*(1-t)))
    certify('general U_j integration-by-parts flux',(j+1)*(1-t)*w*x+DD(w*x)-((4*n+j+1)*(1-t)*w*x-(1-t)*w*y))
    certify('general J_j integration-by-parts flux',(j+1)*(1-t)**2*x*y+DD((1-t)*x*y)-((3*n+j+1)*(1-t)*x*y-(5*n+j+1)*t*(1-t)*x*y-(1-t)**2*y*y+n*n*(1-t)*w*x))
    # Use independent symbols x=X_n and y=Z_n for the affine period state.
    V={-1:3*y-F(1,2),0:y}
    for k in range(1,6):V[k]=((n+k)*V[k-1]+n*n/(2*n+k))/(3*n+k)
    Y={0:2*n*n*V[-1]/(4*n-1)}
    for k in range(1,6):Y[k]=(k*Y[k-1]+2*n*n*V[k-1])/(4*n+k-1)
    U={k:(y+V[k])/(4*n+k+1) for k in range(6)}
    J={0:x}
    for k in range(5):J[k+1]=((3*n+k+1)*J[k]+n*n*U[k]-Y[k]+Y[k+1])/(5*n+k+1)
    # Independently substitute every generated coefficient into its defining recurrence.
    certify('V_-1 initial moment',n*V[-1]-3*n*V[0]+n/2)
    certify('Y_0 initial moment',(4*n-1)*Y[0]-2*n*n*V[-1])
    for k in range(1,6):
        certify('V_%d moment coefficients'%k,(3*n+k)*V[k]-(n+k)*V[k-1]-n*n/(2*n+k))
        certify('Y_%d moment coefficients'%k,(4*n+k-1)*Y[k]-k*Y[k-1]-2*n*n*V[k-1])
    for k in range(6):certify('U_%d moment coefficients'%k,(4*n+k+1)*U[k]-y-V[k])
    for k in range(5):certify('J_%d moment coefficients'%(k+1),(5*n+k+1)*J[k+1]-(3*n+k+1)*J[k]-n*n*U[k]+Y[k]-Y[k+1])
    def integrate(poly):
        result=Sparse()
        for (pt,px,py,pw,pj),coef in poly.terms.items():
            require(pj==0,'unexpected j in formal integral')
            signature=(px,py,pw)
            if signature==(1,1,0): moment=J[pt]
            elif signature==(0,2,0): moment=Y[pt]
            elif signature==(0,1,1): moment=V[pt]
            elif signature==(1,0,1): moment=U[pt]
            elif signature==(0,0,2): moment=1/(2*n+pt+1)
            else: raise ArithmeticError('unknown formal moment '+str(signature))
            result+=coef*moment
        return result
    yn=lam*(1-t)**2*y+mu*w*(1+t)
    xn=nu*t**3*x+qt*y+w*r
    znext=integrate(t*w*yn);xnext=integrate(xn*yn)
    delta=(28*n**3+50*n*n+29*n+5)/(6*(2*n+1)*(3*n+1)*(3*n+2))
    certify('Z contiguous full identity',znext-nu*y-delta)
    certify('x contiguous endpoint t=1',nu*y+r.substitute({0:1})-znext)
    rho=(n+1)**4/(5*prod(5*n+k for k in range(1,5)))
    eta=-(n+1)**2*(138688*n**7+507872*n**6+772828*n**5+630758*n**4+296881*n**3+80204*n*n+11463*n+666)/(30*(2*n+1)*(3*n+1)*(3*n+2)*(4*n+1)*(4*n+3)*prod(5*n+k for k in range(1,5)))
    theta=(744128*n**9+4138176*n**8+10020608*n**7+13828392*n**6+11948992*n**5+6682909*n**4+2410801*n**3+538853*n*n+67431*n+3582)/(120*(2*n+1)**2*(3*n+1)*(3*n+2)*(4*n+3)*prod(5*n+k for k in range(1,5)))
    for name,got,want in zip(('X','Z','constant'),vector(xnext),(rho,eta,theta)):
        certify('X contiguous '+name+' coefficient',got-want)
    k=-2*(44*n*n-26*n+3)/((2*n-1)*(4*n-1))
    ell=(224*n**3-232*n*n+76*n-7)/(8*(2*n-1)**2*(4*n-1))
    fn=16*x+k*y+ell
    difference=16*xnext+k.shift()*znext+ell.shift()-rho*fn-2*rho*u*(y-gamma)
    for label,coef in zip(('X','Z','constant'),vector(difference)):certify('full-count first difference '+label,coef)
    certify('gamma transport',delta+nu*gamma-gamma.shift()+F(27,8)*nu*v)
    certify('gamma initial condition',gamma.value(1)-F(1,3))
    # Dimensionless rank reduction: N is scaled to 1 by homogeneity;
    # x=N^5 G, y=N^3 H. This retains every independent coefficient.
    c=F(1,2);I=y-F(1,8);ew=2*I-y;ea=2*y-c
    q1=-4*y+1
    q2=16*x-8*I-4*ew+2*ea+2*c*q1
    certify('rank open-chain q2',q2-(16*x-12*y+2))
    uw=3*n*y/(4*n-1)-n/(2*(4*n-1))
    tr=-1/(2*n-1);tr2=16*uw-16*y+3
    certify('trace square rank expansion',16*uw-8*ew-16*I+4*c*c+4*ea-tr2)
    certify('full-count rank reduction',tr*tr/8-tr2/4-q1*tr/2+q2-fn)
    certify('literal P(n+1)',P.shift()-P_next_printed)
    certify('literal Q(n+1)',Q.shift()-Q_next_oeis)
    shifted={}
    for name,poly in [('P',P),('Q',Q)]:
        a=poly.shift();require(a.den==1 and all(z>0 for z in a.num.c),name+' positivity failed')
        shifted[name]=list(reversed(a.num.c));checks.append(name+' positive shifted coefficients')
    R=-u.shift()/u*prod(5*n+h for h in range(1,6))/(prod(3*n+h for h in range(1,4))*(n+1)**2)
    S=-v.shift()/v*prod(3*n+h for h in range(1,4))/(n+1)**3
    Omega=R.shift()*S
    def ore(A,B):
        out=[Rat()]*(len(A)+len(B)-1)
        for i,a in enumerate(A):
            for h,b in enumerate(B):out[i+h]+=Rat(a)*Rat(b).shift(i)
        return out
    op=ore([-Omega,1],ore([-R,1],[-1,1]))
    for h,(got,want) in enumerate(zip(op,L_oeis)):certify('literal OEIS E^%d coefficient'%h,L_oeis[3]*got-want)
    degrees=[p.num.degree() for p in L_oeis]
    require(degrees==[24]*4 and all(p.den==1 for p in L_oeis),'OEIS polynomial degree')
    forcing=F(27,4)*u.shift()*v*prod(5*n+h for h in range(1,6))/(prod(3*n+h for h in range(1,4))*(n+1)**2)
    forcing_target=15*prod(5*n+h for h in range(1,5))*Q/(4*(n+1)**4*(n+2)**4*(2*n-1)*(2*n+1)**2*(2*n+3)**2*(3*n+4)*(3*n+5)*(4*n+5)*(4*n+7)*P)
    certify('inhomogeneous forcing',forcing-forcing_target)
    certify('inhomogeneous forcing ratio',forcing.shift()/forcing/rho-Omega)
    # Direct transport of (X,Z,1), independently of the Ore multiplication.
    state=fn;residual=Sparse()
    for h in range(4):
        residual+=L_oeis[h]*state
        state=state.shift().substitute({1:xnext,2:znext})/rho
    for label,coef in zip(('X','Z','constant'),vector(residual)):certify('direct OEIS period elimination '+label,coef)
    moment_receipt={name:{str(i):[z.coefficients() for z in vector(value)] for i,value in moment.items()}
                    for name,moment in [('V',V),('Y',Y),('U',U),('J',J)]}
    return {'certificates':checks,'coefficient_order':'ascending powers of n; state coefficients (X,Z,1)',
            'moments':moment_receipt,'X_shift':[z.coefficients() for z in (rho,eta,theta)],
            'positive_shifted_coefficients_descending':shifted,'OEIS_degrees':degrees},(nu,delta,rho,eta,theta,k,ell)


def literal_count(width):
    # All four literal neighboring comparison families, no prefix rule.
    nodes=5*width;pred=[0]*nodes
    for row in range(5):
        for col in range(width):
            for dr,dc in ((0,1),(1,0),(1,1),(1,-1)):
                r,c=row+dr,col+dc
                if 0<=r<5 and 0<=c<width:pred[r*width+c]|=1<<(row*width+col)
    full=(1<<nodes)-1
    @lru_cache(None)
    def count(mask):
        if mask==full:return 1
        value=0;remaining=full^mask
        while remaining:
            bit=remaining&-remaining;remaining-=bit;index=bit.bit_length()-1
            if mask&pred[index]==pred[index]:value+=count(mask|bit)
        return value
    value=count(0)
    return value,count.cache_info().currsize


def kernel_periods(width):
    # Integrate the piecewise W kernel over each triangular half separately.
    N=factorial(width);yp={};xp={};hom=F(0)
    for h in range(width):
        c=F((-1)**h,factorial(width-1-h)*factorial(width+h))
        yp[width+h]=N*N*c;xp[width+h]=N*N*c/(2*width-h)
        hom+=N*N*c*(F(1,2*width+h+1)-F(1,2*width-h))
    xp[3*width]=hom
    Z=sum((c/F(k+width+1) for k,c in yp.items()),F(0))
    X=sum((a*b/F(i+h+1) for i,a in xp.items() for h,b in yp.items()),F(0))
    require(sum(xp.values())==Z,'kernel x endpoint')
    require(sum(yp.values())==F(width*width,2*width-1),'kernel y endpoint')
    require(hom==F((-1)**width*N**3,factorial(3*width)),'kernel leading coefficient')
    return X,Z


def finite_tests(parameters):
    nu,delta,rho,eta,theta,k,ell=parameters
    def H(i):return (-1)**i*u.value(i)*F(factorial(5*i),factorial(3*i)*factorial(i)**2)
    def I(i):return (-1)**i*v.value(i)*F(factorial(3*i),factorial(i)**3)
    inner=F(0);outer=F(0);records=[];values={};periods={}
    for width in range(1,21):
        actual,states=literal_count(width);X,Z=kernel_periods(width)
        M=F(factorial(5*width),factorial(width)**5)
        derived=M*(16*X+k.value(width)*Z+ell.value(width))
        nested=1-F(27,4)*outer
        require(actual==derived==nested,'literal/kernel/nested mismatch n='+str(width))
        values[width]=actual;periods[width]=(X,Z)
        records.append({'n':width,'count':actual,'graph_states':states,'X':str(X),'Z':str(Z)})
        outer+=H(width)*inner;inner+=I(width)
    require([values[i] for i in (1,2,3)]==[1,1,16],'initial values')
    for i in range(1,20):
        X,Z=periods[i]
        require(periods[i+1]==(rho.value(i)*X+eta.value(i)*Z+theta.value(i),nu.value(i)*Z+delta.value(i)), 'finite moment shift')
        M=F(factorial(5*i),factorial(i)**5)
        require(values[i+1]-values[i]==2*M*u.value(i)*(Z-gamma.value(i)),'finite first difference')
    for i in range(1,18):require(sum(c.value(i)*values[i+h] for h,c in enumerate(L_oeis))==0,'finite OEIS residual')
    zero=sum(c.value(0)*a for c,a in zip(L_oeis,(1,1,1,16)))
    require(zero==5621993879040000,'n=0 residual')
    return {'literal_kernel_nested_checks':records,'initial_values':[1,1,16],
            'n0_empty_array_residual':int(zero),'initial_parameters':{'u1':str(u.value(1)),'v1':str(v.value(1)),'H1':str(H(1)),'H2':str(H(2)),'I1':str(I(1))}}


def matchings(vertices):
    if not vertices:
        yield (),1
        return
    first=vertices[0]
    for h in range(1,len(vertices)):
        partner=vertices[h]
        remaining=vertices[1:h]+vertices[h+1:]
        for edges,sign in matchings(remaining):
            yield ((first,partner),)+edges,(-1)**(h+1)*sign


def matching_classes():
    """Check all 15^2 bordered-Pfaffian terms, including orientation signs."""
    counts={};pairings=list(matchings(tuple(range(6))))
    require(len(pairings)==15,'number of bordered matchings')
    for aa,sa in pairings:
        for ee,se in pairings:
            maps=[]
            for edges in (aa,ee):
                adjacency={}
                for left,right in edges:adjacency[left]=right;adjacency[right]=left
                maps.append(adjacency)
            sign=sa*se
            # Start at the A-border edge (b); end at the E-border edge (1).
            start=maps[0][5];visited={start};at=start;colour=1;path=[at]
            while maps[colour][at]!=5:
                to=maps[colour][at]
                sign*=1 if at<to else -1
                visited.add(to);path.append(to);at=to;colour=1-colour
            require(colour==1 and len(path) in (1,3,5),'alternating border path')
            cycles=[]
            while len(visited)<5:
                at=min(set(range(5))-visited);start=at;length=0;colour=1
                while True:
                    visited.add(at);to=maps[colour][at]
                    require(to!=5,'unexpected cycle border')
                    sign*=1 if at<to else -1
                    at=to;colour=1-colour;length+=1
                    if at==start:break
                require(colour==1 and length in (2,4),'alternating cycle')
                cycles.append(length)
            key=(len(path),tuple(sorted(cycles)),sign)
            counts[key]=counts.get(key,0)+1
    expected={(1,(2,2),1):15,(1,(4,),-1):30,(3,(2,),-1):60,(5,(),1):120}
    require(counts==expected,'Pfaffian sign-class enumeration')
    return [{'ordinary_path_vertices':p,'ordinary_cycle_lengths':list(c),'sign':s,'terms':count}
            for (p,c,s),count in sorted(counts.items())]


def transpose(a): return list(map(list,zip(*a)))
def matmul(a,b):
    bt=transpose(b)
    return [[sum(x*y for x,y in zip(row,col)) for col in bt] for row in a]
def determinant(a):
    a=[list(map(F,row)) for row in a];answer=F(1)
    for i in range(len(a)):
        pivot=next((h for h in range(i,len(a)) if a[h][i]),None)
        if pivot is None:return F(0)
        if pivot!=i:a[pivot],a[i]=a[i],a[pivot];answer=-answer
        value=a[i][i];answer*=value
        for h in range(i+1,len(a)):
            ratio=a[h][i]/value
            for k in range(i+1,len(a)):a[h][k]-=ratio*a[i][k]
    return answer

def pfaffian(a):
    if not a:return 1
    total=0
    for h in range(1,len(a)):
        ids=[i for i in range(len(a)) if i not in (0,h)]
        total+=(-1)**(h+1)*a[0][h]*pfaffian([[a[i][j] for j in ids] for i in ids])
    return total


def discrete_pfaffians():
    records=[]
    for size,seed in [(5,2),(6,3),(7,5)]:
        K=[[((i+2)*(j+3)+seed*(i-j)**2+3*i*j*j)%11-5 for j in range(size)] for i in range(size)]
        E=[[(1 if j>i else 0)-(1 if j<i else 0) for j in range(size)] for i in range(size)]
        A=matmul(matmul(K,E),transpose(K));b=[sum(row) for row in K];B=matmul(E,A)
        ids=list(combinations(range(size),5));total=0
        for ii in ids:
            value=sum(determinant([[K[i][j] for j in jj] for i in ii]) for jj in ids)
            augmented=[[A[i][j] for j in ii]+[b[i]] for i in ii]+[[-b[i] for i in ii]+[0]]
            require(value==pfaffian(augmented),'discrete first bordered Pfaffian')
            total+=value
        tr=sum(B[i][i] for i in range(size));B2=matmul(B,B);tr2=sum(B2[i][i] for i in range(size))
        q1=sum(b[i]*sum(B[i]) for i in range(size));q2=sum(b[i]*sum(B2[i]) for i in range(size))
        traced=sum(b)*(F(tr*tr,8)-F(tr2,4))-F(q1*tr,2)+q2
        require(total==traced,'discrete second bordered Pfaffian')
        records.append({'size':size,'seed':seed,'sum_of_minors':int(total)})
    return records


def main():
    symbolic,parameters=uniform()
    receipt={'status':'PASS','method':'Exact coefficient identities over Q(n); no interpolation or fitting',
             'uniform':symbolic,'finite_sanity_only':finite_tests(parameters),
             'all_225_matching_terms':matching_classes(),'discrete_pfaffian_sanity':discrete_pfaffians(),
             'asymptotic_certificate':verify_asymptotics()}
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__':main()
