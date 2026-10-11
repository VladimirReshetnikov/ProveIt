"""Replay exact fifth-power and mixed-polygamma bookkeeping.

Run: python verify_fifth.py
The script checks symbolic algebra, finite harmonic identities, all
asymptotic constants, spectral extraction, and primitive derivatives.
It does not certify floating-point quadrature or global priority.
"""
import json
from pathlib import Path
from harmonic_algebra import *

checks=[]
def check(name,expr):
    val=s.expand(expr)
    if val!=0:raise AssertionError((name,val))
    checks.append(name)

def check_words(name,a,bb):
    for w,v in combine(a,scale(bb,-1)).items():
        if s.expand(v)!=0:raise AssertionError((name,w,v))
    checks.append(name)

psi=-1/x+b+c*x+d*x*x+e*x**3+f*x**4
P5=s.expand(psi**5)
PI=s.expand(psi*s.diff(psi,x)**2)
ps5={1:-5*b**4+30*b*b*c-20*b*d-10*c*c+5*e,2:10*b**3-20*b*c+5*d,3:-10*b*b+5*c,4:5*b,5:-1}
psI={1:4*b*d+c*c-5*e,2:2*b*c-3*d,3:-c,4:b,5:-1}
kap5=-g**5+20*g**3*z2-30*g*g*z3-30*g*z2*z2+20*g*z4+20*z2*z3-5*z5
kapI=-g*z2*z2-6*g*z4-2*z2*z3+7*z5
for name,P,ps,kap in [('Q5',P5,ps5,kap5),('I',PI,psI,kapI)]:
    for j in range(1,6):check(name+'_principal_'+str(j),P.coeff(x,-j)-ps[j])
    check(name+'_kappa',P.coeff(x,0).subs({b:-g,c:z2,d:-z3,e:z4,f:-z5})-kap)

def difference(p):
    return s.expand(s.sympify(p).subs({b:b+t,c:c+t*t,d:d+t**3,e:e+t**4,f:f+t**5})-p)

expected_diff5={1:-20*b**3*t+60*b*c*t+20*b*t**3+10*c*t*t-20*d*t,2:30*b*b*t+10*b*t*t-20*c*t-5*t**3,3:-20*b*t-5*t*t,4:5*t,5:0}
expected_diffI={1:4*d*t+2*c*t*t+4*b*t**3,2:2*c*t+2*b*t*t-t**3,3:-t*t,4:t,5:0}
for name,ps,ed in [('Q5',ps5,expected_diff5),('I',psI,expected_diffI)]:
    for j in range(1,6):check(name+'_difference_'+str(j),difference(ps[j])-ed[j])

# The finite sums S5(N) and SI(N), before any limit.
A=g**3-3*g*z2+z3
r0=ps5[1].subs({b:-g,c:z2,d:-z3,e:z4})
C0=4*g*z3+z2*z2-5*z4
w=lambda *args:word(tuple(args))
e2=w(1,1)
S5=combine(w(1,1,1,1,1), {})
S5=combine(scale(w(1,1,1,1,1),-120),scale(w(1,1,1,1),120*g),scale(w(1,1,1),60*(z2-g*g)),scale(e2,20*A),scale(w(1),r0),scale(w(2),20*A),scale(w(2,1,1,1),-120),scale(w(2,1,1),120*g),scale(w(2,1),50*z2-60*g*g),scale(mul(e2,w(3)),20),scale(w(3,1,1),-20),scale(mul(w(1),w(4)),-20),scale(w(4,1),20),scale(w(5),20),scale(mul(w(1),w(2,2)),10),scale(w(2,1,2),-10),scale(w(2,2,1),-10),scale(w(2,3),10),scale(mul(w(1),w(3)),-20*g),scale(w(3,1),20*g),scale(mul(w(1),w(2)),10*z2))
SI=combine(scale(mul(e2,combine(w(3),word((),-z3))),4),mul(w(1),combine(scale(w(2,2),2),scale(w(4),-4),scale(w(3),-4*g),scale(w(2),2*z2),word((),C0))),scale(w(3,1,1),-4),scale(w(2,1,2),-2),scale(w(2,2,1),-2),scale(w(2,3),2),scale(w(4,1),4),scale(w(5),4),scale(w(3,1),4*g),scale(w(2),-4*z3),scale(w(2,1),-2*z2))
check_words('Q5_exact_finite_sum',sum_inner(to_words(ps5[1]),1,True),S5)
check_words('I_exact_finite_sum',sum_inner(to_words(psI[1]),1,True),SI)

C5=-g**5+30*g**3*z2-80*g*g*z3-s.Rational(65,2)*g*z4+60*z2*z3-69*z5
CI=g*z4-12*z2*z3+15*z5
K5=30*g*g*z2-60*g*z3+s.Rational(35,3)*z4
KI=-2*g*z3+s.Rational(35,6)*z4

def nonlog_constant(ps,kap):
    total=kap
    for j in range(2,6):
        for (po,),coef in s.Poly(difference(ps[j]),t).terms():
            total+=ev(sum_inner(to_words(coef),j-1+po,False))/(j-1)
        total-=ev(sum_inner(to_words(s.sympify(ps[j])),j,True))
    return reduce_mzv(total)

for name,ps,kap,C,K in [('Q5',ps5,kap5,C5,K5),('I',psI,kapI,CI,KI)]:
    check(name+'_finite_constant',reduce_mzv(ev(sum_inner(to_words(ps[1]),1,True)))-C)
    check(name+'_nonlog_constant',nonlog_constant(ps,kap)-C-K)

# Full polynomial in log N, including every nonzero divergent term.
ell=s.symbols('ell')
E=[s.Integer(1)]
for j in range(1,6):
    E.append(s.expand(sum((-1)**(r-1)*({1:ell+g,2:z2,3:z3,4:z4,5:z5}[r])*E[j-r] for r in range(1,j+1))/j))
sub_mzv={zs(w):v for w,v in ordinary.items()}
def asymptotic_eval(words):
    # CT algorithm works with gamma replaced by ell+gamma in H1 alone.
    def rg(word):
        if not word:return s.Integer(1)
        if word==(1,):return ell+g
        if word[0]!=1:return zs(word)
        st=dict(stuffle((1,),word[1:]));n=st.pop(word)
        return s.expand(((ell+g)*rg(word[1:])-sum(v*rg(k) for k,v in st.items()))/n)
    ans=s.expand(sum(v*rg(word) for word,v in words.items()))
    return s.expand(ans.subs(sub_mzv)).subs(z2*z2,s.Rational(5,2)*z4).expand()
check('Q5_full_finite_asymptotic',asymptotic_eval(S5)-(-ell**5+20*z2*ell**3-90*z4*ell+C5))
check('I_full_finite_asymptotic',asymptotic_eval(SI)-CI)
check('Q5_boundary_asymptotic',s.expand(ps5[1].subs({b:ell,c:2*z2,d:0,e:2*z4})*ell).subs(z2*z2,s.Rational(5,2)*z4)-(-5*ell**5+60*z2*ell**3-90*z4*ell))

# Low-degree regression against the independently inspected cubic/quartic reports.
for k,K in [(3,3*z2),(4,-12*g*z2+12*z3+18*z4)]:
    P=s.expand(psi**k);ps={j:P.coeff(x,-j) if j<=k else s.Integer(0) for j in range(1,6)}
    kap=P.coeff(x,0).subs({b:-g,c:z2,d:-z3,e:z4,f:-z5})
    C=reduce_mzv(ev(sum_inner(to_words(ps[1]),1,True)))
    check('known_power_'+str(k),nonlog_constant(ps,kap)-C-K)

# Primitive kernels and all fixed derivative orders r=1,...,8.
n,z=s.symbols('n z',positive=True)
for j in range(1,6):
    F=s.log(1+z/n)-z/n if j==1 else ((n+z)**(1-j)-n**(1-j))/(1-j)-z/n**j
    check('primitive_kernel_'+str(j),s.cancel(s.diff(F,z)-((n+z)**(-j)-n**(-j))))
    for r in range(1,9):
        check('derivative_kernel_'+str(j)+'_'+str(r),s.cancel(s.diff((n+z)**(-j),z,r)-(-1)**r*s.factorial(r)*s.binomial(r+j-1,j-1)*(n+z)**(-r-j)))

# Spectral linear coefficient extraction, with lambda1 = -gamma1.
lam1,eta,theta,xi,Rp,Z31p,Z22p,zp2,zp3=s.symbols('lambda1 eta theta xi Rprime Z31prime Z22prime zeta2prime zeta3prime')
Flinear=6*xi-6*g*theta+3*(g*g-z2)*eta-(g**3-3*g*z2+2*z3)*lam1-Rp
Jprime=2*Rp+2*Z31p+Z22p-2*g*zp3+z2*zp2
raw=K5-20*Flinear+20*Z31p-20*g*zp3+10*Z22p+10*z2*zp2
boxed=K5-120*xi+120*g*theta-60*(g*g-z2)*eta+20*(g**3-3*g*z2+2*z3)*lam1+10*Jprime
check('Q5_spectral_bridge',raw-boxed)
check('I_spectral_bridge',KI+4*Rp+4*Z31p+2*Z22p-4*g*zp3+2*z2*zp2-(KI+2*Jprime))

# Integration-by-parts endpoint ledger for the inverse-Gamma Bell polynomial.
endpoints=[12*g*g*z2-12*g*z3-11*z4,2*g*z3+s.Rational(3,2)*z4,-6*z4,8*z4,0]
functions=[psi**4,psi**2*s.diff(psi,x),s.diff(psi,x)**2,psi*s.diff(psi,x,2),s.diff(psi,x,3)]
at_one=[g**4,g*g*z2,z2*z2,2*g*z3,6*z4]
for j,(fun,one,target) in enumerate(zip(functions,at_one,endpoints)):
    ct=s.expand(fun).coeff(x,0).subs({b:-g,c:z2,d:-z3,e:z4,f:-z5})
    check('endpoint_'+str(j),s.expand(one-ct-target).subs(z2*z2,s.Rational(5,2)*z4))
endcombo=s.Rational(5,2)*endpoints[0]-10*endpoints[1]+s.Rational(5,2)*endpoints[2]+5*endpoints[3]-endpoints[4]
check('A5_integration_by_parts_endpoint',endcombo-(30*g*g*z2-50*g*z3-s.Rational(35,2)*z4))
check('A5_raw_compatibility',K5-5*KI-endcombo)

result={'all_passed':True,'exact_checks':len(checks),'checks':checks,'method':'Exact finite harmonic quasi-shuffle identities, explicit standard weight<=5 MZV reductions, and polynomial algebra. Numerical evidence is in a separate file.'}
out=Path(__file__).resolve().parent.parent / 'results' / 'fifth_exact_results.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'all_passed':True,'exact_checks':len(checks),'output':str(out)},indent=2))
