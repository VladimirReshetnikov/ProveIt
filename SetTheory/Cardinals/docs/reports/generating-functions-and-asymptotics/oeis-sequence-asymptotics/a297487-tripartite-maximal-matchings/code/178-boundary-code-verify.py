#!/usr/bin/env python3
"""Exact finite checks for Report178. Python standard library; no floating point.

All acceptance and rejection checks remain active under python -O. Mathematical
proofs of remainders and uniformity are in the manuscript, not established by
these finite tests. Q(a) is represented by three rational coordinates, a^3=1/4.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from functools import lru_cache
import json
from math import comb, factorial
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent.parent

class VerificationError(ValueError):
    pass

def need(condition, message):
    if not condition:
        raise VerificationError(message)

def integer(value, name, minimum=0):
    need(type(value) is int and value >= minimum, name + ' must be an integer >= ' + str(minimum))

def rational(value):
    need(type(value) in (int, F), 'exact rational required (no bool or float)')
    return F(value)

class A:
    """Field Q[a]/(a^3-1/4), with inversion by exact Gaussian elimination."""
    __slots__ = ('c',)
    def __init__(self, value=0):
        if isinstance(value, A):
            self.c = value.c
        elif type(value) is tuple:
            need(len(value) == 3, 'field coordinates must have length three')
            self.c = tuple(rational(x) for x in value)
        else:
            self.c = (rational(value), F(0), F(0))
    def __add__(self, other):
        other = A(other)
        return A(tuple(x+y for x,y in zip(self.c, other.c)))
    __radd__ = __add__
    def __neg__(self):
        return A(tuple(-x for x in self.c))
    def __sub__(self, other):
        return self + -A(other)
    def __rsub__(self, other):
        return A(other) + -self
    def __mul__(self, other):
        other = A(other); c = [F(0)]*5
        for i,x in enumerate(self.c):
            for j,y in enumerate(other.c): c[i+j] += x*y
        for i in (4,3): c[i-3] += c[i]/4
        return A(tuple(c[:3]))
    __rmul__ = __mul__
    def inverse(self):
        need(bool(self), 'division by zero in Q(a)')
        columns = [(self*A(tuple(F(i == k) for i in range(3)))).c for k in range(3)]
        matrix = [[columns[j][i] for j in range(3)] + [F(i == 0)] for i in range(3)]
        for j in range(3):
            pivot = next((i for i in range(j,3) if matrix[i][j]), None)
            need(pivot is not None, 'singular field inversion')
            matrix[j], matrix[pivot] = matrix[pivot], matrix[j]
            divisor = matrix[j][j]; matrix[j] = [x/divisor for x in matrix[j]]
            for i in range(3):
                if i != j:
                    multiple = matrix[i][j]
                    matrix[i] = [x-multiple*y for x,y in zip(matrix[i],matrix[j])]
        return A(tuple(matrix[i][3] for i in range(3)))
    def __truediv__(self, other): return self*A(other).inverse()
    def __rtruediv__(self, other): return A(other)*self.inverse()
    def __pow__(self, power):
        need(type(power) is int, 'field exponent must be an integer')
        if power < 0: return self.inverse()**(-power)
        value, base = A(1), self
        while power:
            if power & 1: value *= base
            base *= base; power //= 2
        return value
    def __bool__(self): return any(self.c)
    def __eq__(self, other):
        try: return self.c == A(other).c
        except VerificationError: return False
    def __repr__(self): return 'A'+repr(self.c)

a = A((0,1,0))

def trim(p):
    p = list(p)
    while p and not p[-1]: p.pop()
    return p

def add(p,q):
    r = list(p)+[F(0)]*max(0,len(q)-len(p))
    for k,x in enumerate(q): r[k] += x
    return trim(r)

def scale(p,c): return trim([x*c for x in p])

def multiply(p,q):
    if not p or not q: return []
    r = [F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): r[i+j] += x*y
    return trim(r)

def derivative(p): return trim([k*p[k] for k in range(1,len(p))])

def evaluate(p,x):
    r = 0
    for c in reversed(p): r = r*x+c
    return r

@lru_cache(None)
def _bernoulli(n):
    if n == 0: return F(1)
    return -sum(F(comb(n+1,k))*_bernoulli(k) for k in range(n))/F(n+1)

def bernoulli(n):
    integer(n,'Bernoulli index')
    return _bernoulli(n)

def faulhaber(m):
    """Polynomial sum_{h=0}^{x-1} h^m, B1=-1/2 convention."""
    integer(m,'power')
    r = [F(0)]*(m+2)
    for k in range(m+1): r[m+1-k] = F(comb(m+1,k),m+1)*bernoulli(k)
    return trim(r)

def binomial_integer(n,k):
    integer(k,'binomial lower index')
    need(type(n) is int, 'binomial upper index must be integer')
    v = F(1)
    for j in range(k): v *= F(n-j,j+1)
    return v

def phase(order,s,u,boundary=False):
    """Finite Faulhaber/Stirling prescription through q^order.

    Dictionary indexed by q exponent; each value is polynomial in y. This
    function is algorithmic at every requested nonnegative order, not an
    assertion of convergence of the infinite formal expression.
    """
    integer(order,'order')
    need(type(s) in (F,A) and type(u) in (F,A), 'phase parameters must be exact')
    need(bool(s) and bool(u), 'phase parameters must be nonzero')
    out = {}
    def term(qpower,ypower,c):
        if qpower > order or not c: return
        p = [F(0)]*ypower+[c]
        out[qpower] = add(out.get(qpower,[]),p)
    if boundary:
        need(s == a and u == 2*a, 'boundary coordinates require s=a,u=2a')
        term(-2,0,3*s);term(-1,1,F(3))
        # 3x(1-log(1+yq/a))-log(1+yq/a)
        for k in range(1,order+3):
            c=F((-1)**(k+1),k)/s**k
            term(k-2,k,-3*s*c);term(k-1,k+1,-3*c);term(k,k,-c)
    else:
        term(-1,1,F(3))
        for t,d in ((s,1),(u,2)):
            for k in range(1,order+3):
                c=F((-1)**(k+1),k)*(F(d)/t)**k
                term(k-2,k,-t*c);term(k-1,k+1,-d*c);term(k,k,-c/2)
    for m in range(1,order+3):
        for k,c in enumerate(faulhaber(m)):
            for ell in range(k+1):
                term(3*m-2*k+ell,ell,-F(2,m)*c*comb(k,ell)*s**(k-ell))
    for r in range(1,(order+2)//4+1):
        power=1-2*r; c=-bernoulli(2*r)/F(2*r*(2*r-1))
        for t,d in ((s,1),(u,2)):
            for ell in range(order+2*power+1):
                term(-2*power+ell,ell,c*t**power*binomial_integer(power,ell)*(F(d)/t)**ell)
    return {k:trim(v) for k,v in out.items() if trim(v)}

def moments(b,v,degree):
    integer(degree,'moment degree')
    mu=[b*0+1]
    if degree: mu.append(b)
    for k in range(1,degree): mu.append(b*mu[k]+k*v*mu[k-1])
    return mu

def average(p,b,v):
    mu=moments(b,v,max(0,len(p)-1))
    return sum((x*mu[k] for k,x in enumerate(p)),b*0)

def coefficients(order,s,u,boundary=False):
    H=phase(order,s,u,boundary);chi=4/u+1/s;b=-2*s/chi;v=1/chi
    P=[[s*0+1]]
    for k in range(1,order+1):
        p=[]
        for r in range(1,k+1): p=add(p,scale(multiply(H.get(r,[]),P[k-r]),F(r,k)))
        P.append(p)
    c=[average(p,b,v) for p in P]
    log=[s*0]
    for k in range(1,order+1):
        log.append(c[k]-sum((F(j,k)*log[j]*c[k-j] for j in range(1,k)),s*0))
    E={}
    for power in (1,2):
        vals=[]
        for k in range(order+1):
            vals.append(average([F(0)]*power+P[k],b,v)-sum((c[j]*vals[k-j] for j in range(1,k+1)),s*0))
        E[power]=vals
    variance=[E[2][k]-sum((E[1][j]*E[1][k-j] for j in range(k+1)),s*0) for k in range(order+1)]
    return H,P,c,log,E[1],variance

def formulas(u):
    x=u**3
    return [
        (60*x**4+315*x**3+372*x**2+80*x-64)/(6*u**8*(x+4)**3),
        -(5*x**8-340*x**7-900*x**6+6056*x**5+17240*x**4-4800*x**3-30720*x**2-7680*x+6144)/(60*u**10*(x+4)**5),
        -(3*x*x+7*x-8)/(x+4)**3,
        -4*(x*x+2*x+4)/(u*(x+4)**3),
    ]

def poisson_average(p,lam):
    # Touchard raw moments, using exact Stirling numbers of the second kind.
    rows=[[1]]
    for n in range(1,len(p)):
        old=rows[-1]; row=[0]*(n+1)
        for k in range(1,n+1): row[k]=(old[k-1] if k-1<len(old) else 0)+k*(old[k] if k<len(old) else 0)
        rows.append(row)
    return sum((c*sum(F(z)*lam**k for k,z in enumerate(rows[n])) for n,c in enumerate(p)),F(0))

def exterior(order,c):
    """All-order finite-product log followed by Poisson moments."""
    integer(order,'exterior order');need(type(c) is F and c>0,'positive rational exterior ratio required')
    H=[[]]
    for m in range(1,order+1):
        S=faulhaber(m)
        # sum_{h=1}^{2j} h^m = S_m(2j)+(2j)^m
        T=[x*2**k for k,x in enumerate(S)]
        if len(T)<=m:T += [F(0)]*(m+1-len(T))
        T[m] += 2**m
        H.append(add(scale(S,-F(2,m)),scale(T,F((-1)**m,m)/c**m)))
    P=[[F(1)]]
    for k in range(1,order+1):
        row=[]
        for r in range(1,k+1):row=add(row,scale(multiply(H[r],P[k-r]),F(r,k)))
        P.append(row)
    return H,P,[poisson_average(p,c**-2) for p in P]

def validate_parts(parts):
    need(type(parts) is tuple and len(parts)==3,'parts must be a tuple of three integers')
    for x in parts: integer(x,'part size')

@lru_cache(None)
def _graph(parts,unmatched):
    if not any(parts):return 1
    i=next(k for k,x in enumerate(parts) if x);rr=list(parts);rr[i]-=1
    count=_graph(tuple(rr),i) if unmatched in (-1,i) else 0
    for j,nj in enumerate(rr):
        if i!=j and nj:
            qq=rr.copy();qq[j]-=1;count+=nj*_graph(tuple(qq),unmatched)
    return count

def graph(parts,unmatched=-1):
    # Validate before cached worker: cached values cannot bypass type guards.
    validate_parts(parts);need(type(unmatched) is int and unmatched in (-1,0,1,2),'invalid unmatched part')
    return _graph(parts,unmatched)

def divide_exact(numerator,denominator):
    q,r=divmod(numerator,denominator);need(r==0,'nonintegral labeled branch count');return q

def branches(parts):
    validate_parts(parts);carrier=1
    for p in parts:carrier*=factorial(p)
    ans=[];perfect=0
    for i in range(3):
        count=0
        for k in range(parts[i]+1):
            rem=list(parts);rem[i]-=k
            edges=[rem[1]+rem[2]-rem[0],rem[0]+rem[2]-rem[1],rem[0]+rem[1]-rem[2]]
            if any(x<0 or x%2 for x in edges):continue
            denominator=factorial(k)
            for x in edges:denominator*=factorial(x//2)
            term=divide_exact(carrier,denominator);count+=term
            if k==0:
                if i:need(perfect==term,'inconsistent perfect duplicate')
                perfect=term
        ans.append(count)
    return sum(ans)-2*perfect,ans,perfect

def big_branch(n,d):
    integer(n,'n');need(type(d) is int and 2*n+d>=0,'invalid imbalance')
    carrier=factorial(2*n+d)*factorial(n)**2
    return sum(divide_exact(carrier,factorial(n-j)**2*factorial(d+2*j)*factorial(j))
               for j in range(max(0,(-d+1)//2),n+1))

def encode(value):
    if type(value) is A:return [str(x) for x in value.c]
    if type(value) is F:return str(value)
    if type(value) in (list,tuple):return [encode(x) for x in value]
    if type(value) is dict:return {str(k):encode(v) for k,v in value.items()}
    return value

def same(expected,actual,path='root'):
    need(type(expected) is type(actual),'type mismatch at '+path)
    if type(expected) is dict:
        need(expected.keys()==actual.keys(),'field set mismatch at '+path)
        for key in expected:same(expected[key],actual[key],path+'.'+key)
    elif type(expected) is list:
        need(len(expected)==len(actual),'length mismatch at '+path)
        for i,(x,y) in enumerate(zip(expected,actual)):same(x,y,path+'['+str(i)+']')
    else:need(expected==actual,'value mismatch at '+path)

PREFIX=[1,3,74,4506,489240,82306920,19743705360,6381638963280,2667409223310720,1397546505279388800,895714536024011692800]

def derive():
    H,P,c,logs,mean,var=coefficients(4,a,2*a,True)
    other=coefficients(4,a,2*a,False)
    need(all(H.get(k,[])==other[0].get(k,[]) for k in range(-1,5)),'boundary and moving phase disagree')
    expected_c=[A(1),211*a/216,172781*a*a/466560,A(F(-189855337,1209323520)),-6247138084769*a/36569943244800]
    expected_l=[A(0),211*a/216,-173*a*a/1620,A(F(-55,324)),-389*a/122472]
    expected_mean=[-2*a*a/3,A(F(-1,12)),49*a/162,-173*a*a/972,A(F(1,162))]
    expected_var=[a/3,-4*a*a/9,A(F(1,12)),17*a/243,-217*a*a/2916]
    for label,actual,target in [('c',c,expected_c),('log',logs,expected_l),('mean y',mean,expected_mean),('variance y',var,expected_var)]:
        need(actual==target,'boundary '+label+' coefficients differ')
    need(H[-2]==[3*a] and H[-1]==[-a*a],'leading boundary phase differs')
    need(H[0]==[-a**3/3,-2*a,-3/(2*a)],'constant boundary phase differs')
    need(-a**3/3+2*a*a/(3/a)==F(1,12),'completed-square constant differs')
    need(logs[3]+F(1,24)==F(-83,648),'factorial correction differs')
    extension=coefficients(6,a,2*a,True)
    moving_extension=coefficients(6,a,2*a,False)
    need(extension[2][:5]==c and extension[3][:5]==logs, 'higher-order prefix consistency failed')
    need(extension[2]==moving_extension[2] and extension[4:]==moving_extension[4:], 'order-six boundary/moving algorithms disagree')
    need(extension[2][5]==-542049980586199*a*a/7899107740876800 and extension[2][6]==F(841227275350329073,29249267520503808000), 'independent symbolic order-five/six relative checks differ')
    need(extension[3][5]==-3679*a*a/2099520 and extension[3][6]==F(151,8748), 'independent symbolic order-five/six log checks differ')
    need(extension[4][5:]==[97*a/52488,9211*a*a/157464] and extension[5][5:]==[A(F(1,162)),679*a/157464], 'order-five/six moments differ')
    moving=[]
    points=[F(1,3),F(1,2),F(2,3),F(1),F(3,2),F(2),F(3),F(5)]
    for u in points:
        s=1/u**2;HH,PP,cc,ll,mm,vv=coefficients(2,s,u)
        target=formulas(u)
        need([cc[1],ll[2],mm[1],vv[1]]==target,'moving formulas differ at '+str(u))
        h1=[s-s**4/6,-(s*s+1/(2*s)+1/u),F(-1),1/(6*s*s)+4/(3*u*u)]
        h2=[-s**5/10+s*s/2-(1/s+1/u)/12,-2*s**3/3+1,-s+1/(4*s*s)+1/(u*u),F(0),-1/(12*s**3)-4/(3*u**3)]
        need(HH[1]==h1 and HH[2]==h2,'independent first phase polynomials differ')
        chi=4/u+1/s;b=-2*s/chi;v=1/chi
        need(v*average(derivative(h1),b,v)==target[2],'mean integration by parts differs')
        need(v*v*average(derivative(derivative(h1)),b,v)==target[3],'variance integration by parts differs')
        moving.append({'u':u,'delta':u-2/u**2,'phase_h1':h1,'phase_h2':h2,'c1':cc[1],'c2':cc[2],'ell2':ll[2],'m0':mm[1],'v1':vv[1]})
    need(formulas(2*a)==[c[1],logs[2],A(F(-1,12)),-4*a*a/9],'algebraic moving boundary specialization differs')
    ext=[]
    for ratio in (F(1,3),F(1,2),F(1),F(3,2),F(2),F(3)):
        EH,EP,EC=exterior(2,ratio)
        need(EC[1]==-(ratio**-4+2*ratio**-5+3*ratio**-3),'exterior first correction differs')
        # Independent fixed-j finite-product expansion through second order.
        for j in range(9):
            first=-2*sum(F(h) for h in range(j))-sum(F(h)/ratio for h in range(1,2*j+1))
            second=-sum(F(h*h) for h in range(j))+sum(F(h*h)/(2*ratio*ratio) for h in range(1,2*j+1))
            need(evaluate(EH[1],F(j))==first and evaluate(EH[2],F(j))==second,'exterior finite-product log differs')
            need(evaluate(EP[2],F(j))==second+first*first/2,'exterior exponentiation differs')
        ext.append({'c':ratio,'log_polynomials':EH,'relative_polynomials':EP,'relative_coefficients':EC})
    integer_cases=[]
    for n in range(11):
        for d in range(-n,n+3):
            total,br,perfect=branches((2*n+d,n,n));count=graph((2*n+d,n,n));big=big_branch(n,d)
            need(total==count and br[0]==big,'graph/full branch comparison failed')
            if d>=0:need(total==big,'nonnegative imbalance must have exact large branch')
            if d%2:need(perfect==0,'odd total cannot be perfect')
            integer_cases.append({'n':n,'d':d,'total':total,'branches':br,'perfect':perfect})
    need(len(integer_cases)==143,'integer coverage differs')
    prefix=[big_branch(n,0) for n in range(16)]
    need(prefix[:11]==PREFIX,'boundary prefix differs')
    for n,count in enumerate(prefix):need(count==graph((2*n,n,n)),'extended boundary graph recursion differs')
    return encode({'schema_version':1,'report':178,'scope':{
        'finite_coefficient_checks_only':True,'all_order_remainders_proved_in_manuscript':True,
        'moving_checks':'Eight exact positive rational evaluations and exact Q(a) boundary specialization; finite checks do not prove rational identities',
        'numerical_remainder_bounds_certified':False,'floating_point_used':False},
        'boundary':{'basis':['1','a','a^2'],'relation':'a^3=1/4','order':4,'phase':H,'relative':c,'log_relative':logs,'mean_y':mean,'variance_y':var,'log_A_n_inverse_n':A(F(-83,648)),'counts_n0_to15':prefix},
        'higher_order_check':{'order':6,'relative':extension[2],'log_relative':extension[3],'mean_y':extension[4],'variance_y':extension[5]},'moving':moving,'exterior':ext,'integer_cases':integer_cases})

def reject(call):
    try:call()
    except (VerificationError,TypeError,ValueError,ZeroDivisionError):return
    raise VerificationError('malformed parameter was accepted')

def self_tests():
    need(a**3==F(1,4) and (1+a+a*a)*(1+a+a*a).inverse()==1,'field self-test failed')
    for m in range(9):
        for x in range(9):need(evaluate(faulhaber(m),F(x))==sum(F(h)**m for h in range(x)),'Faulhaber self-test failed')
    graph((2,1,1));bernoulli(1) # Warm cache before type rejection.
    checks=[]
    for bad in (True,False,1.0,'1',F(1),None):
        checks.extend([lambda bad=bad:graph((2,bad,1)),lambda bad=bad:big_branch(bad,0),lambda bad=bad:bernoulli(bad),lambda bad=bad:phase(bad,a,2*a)])
    checks.extend([lambda:A(True),lambda:A(1.0),lambda:A((1,2)),lambda:A(0).inverse(),lambda:graph([2,1,1]),lambda:graph((2,1)),lambda:graph((-1,1,1)),lambda:graph((2,1,1),True),lambda:big_branch(1,-3),lambda:big_branch(1,True),lambda:exterior(1,F(0)),lambda:exterior(1,1.0)])
    for call in checks:reject(call)
    return {'malformed_parameter_rejections':len(checks),'faulhaber_evaluations':81,'warm_cache_type_checks':True}

def unique_object(pairs):
    result={}
    for key,value in pairs:
        need(key not in result,'duplicate JSON key: '+key);result[key]=value
    return result

def load_certificate(path):
    import os,stat
    path=Path(path).absolute()
    need('..' not in path.parts,'unsafe certificate path')
    for parent in reversed(path.parents):need(stat.S_ISDIR(parent.lstat().st_mode),'symlinked/nonregular certificate directory')
    need(stat.S_ISREG(path.lstat().st_mode),'certificate must be a regular non-symlink file')
    flags=os.O_RDONLY|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_NONBLOCK',0)
    with os.fdopen(os.open(path,flags),'r',encoding='utf-8') as handle:
        need(stat.S_ISREG(os.fstat(handle.fileno()).st_mode),'certificate must be regular')
        return json.load(handle,object_pairs_hook=unique_object,parse_constant=lambda x:(_ for _ in ()).throw(VerificationError('nonfinite JSON constant')))

def canonical(data):return json.dumps(data,sort_keys=True,indent=2,allow_nan=False)+'\n'

def manuscript_prefix(path):
    path=Path(path)
    # Share the regular-file/path protections with the strict manifest reader.
    import stat
    absolute=path.absolute()
    need('..' not in absolute.parts, 'unsafe manuscript path')
    for parent in reversed(absolute.parents):need(stat.S_ISDIR(parent.lstat().st_mode), 'symlinked manuscript directory')
    need(stat.S_ISREG(absolute.lstat().st_mode), 'manuscript must be a regular file')
    text=absolute.read_text(encoding='utf-8')
    begin='% BEGIN VERIFIED BOUNDARY PREFIX';end='% END VERIFIED BOUNDARY PREFIX'
    need(text.count(begin)==1 and text.count(end)==1, 'missing/duplicate boundary prefix marker')
    body=text.split(begin,1)[1].split(end,1)[0]
    match=re.fullmatch(r'\s*\\\[\s*(.*?)\s*\\\]\s*',body,re.S)
    need(match is not None, 'boundary prefix must be a single display')
    values=match.group(1).strip()
    if values.startswith(r'\begin{gathered}'):
        need(values.endswith(r'\end{gathered}') and values.count(r'\begin{gathered}')==1 and values.count(r'\end{gathered}')==1,'invalid gathered prefix wrapper')
        values=values[len(r'\begin{gathered}'):-len(r'\end{gathered}')]
    for spacing in (r'\qquad',r'\quad',r'\,',r'\;',r'\:',r'\!',r'\\',r'\ '):
        values=values.replace(spacing,' ')
    need(re.fullmatch(r'\s*\d+(?:\s*,\s*\d+)*\s*\.?\s*',values) is not None, 'nonliteral boundary prefix')
    parsed=[int(x) for x in re.findall(r'\d+',values)]
    need(parsed==PREFIX, 'manuscript boundary prefix differs')
    return len(parsed)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=ROOT/'data/certificates.json')
    parser.add_argument('--manuscript',type=Path,default=ROOT/'Report178.tex')
    args=parser.parse_args();tests=self_tests();data=derive();same(data,load_certificate(args.data));prefix_count=manuscript_prefix(args.manuscript)
    print(canonical({'status':'PASS','report':178,'all_checks_passed':True,'boundary_order':4,'higher_order_checked':6,'manuscript_prefix_values':prefix_count,'moving_rational_points':8,'exterior_rational_points':6,'integer_cases':143,'boundary_graph_cases':16,'parameter_tests':tests,'scope':'Exact finite checks; analytic uniform remainder proofs are in the manuscript'}),end='')

if __name__=='__main__':
    try:main()
    except (VerificationError,ValueError,TypeError,KeyError,OSError,RecursionError) as exc:
        print('VERIFICATION FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
