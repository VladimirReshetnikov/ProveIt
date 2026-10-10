import sympy as s

L=s.symbols('L', real=True)
pi=s.pi
I=s.I
B2,B4,B6,Z3,Z5,lg=s.symbols('G beta4 beta6 zeta3 zeta5 log2',real=True)

def zeta(n):
    if n==3:return Z3
    if n==5:return Z5
    return s.zeta(n)

def Q(n,L):
    return s.expand(-(2*pi*I)**n/s.factorial(n)*s.bernoulli(n,L/(2*pi*I)))

def li(n):
    if n==1:return -lg/2+I*pi/4
    be={2:B2,3:pi**3/32,4:B4,5:5*pi**5/1536,6:B6}[n]
    return -s.Rational(1,2**n)*(1-s.Rational(1,2**(n-1)))*zeta(n)+I*be

def double_zeta(a,b):
    return {(2,1):Z3,(4,1):2*Z5-zeta(2)*Z3,
            (3,2):3*zeta(2)*Z3-s.Rational(11,2)*Z5,
            (2,3):s.Rational(9,2)*Z5-2*zeta(2)*Z3}[(a,b)]

def R_at_one(a,b):
    w=a+b
    ans=Q(w,0)-zeta(w)
    for k in range(b+1):
        ans+=(-1)**k*s.binomial(a+k-1,k)*Q(b-k,0)*zeta(a+k)
    return s.expand(ans)

def constant(a,b):
    if a==1:return (-1)**(b+1)*b*zeta(b+1)
    w=a+b
    p=2*double_zeta(a,b) if w%2 else 0
    return s.expand(p-R_at_one(a,b))

def R(a,b,L):
    ans=Q(a+b,L)-li(a+b)
    for k in range(b+1):
        ans+=(-1)**k*s.binomial(a+k-1,k)*Q(b-k,L)*li(a+k)
    return s.expand(ans)

def g(a,b):
    x=I*pi/2
    p=R(a,b,x)+sum(constant(a-j,b)*x**j/s.factorial(j) for j in range(a))
    p=s.expand(p)
    assert s.simplify(s.re(p))==0,(a,b,p)
    return s.expand(p/(2*I))

targets={
 (5,1):(-64*pi**3*Z3-527*pi*Z5+4096*B6)/2048,
 (4,2):(96*pi**3*Z3-32*pi**2*B4+1581*pi*Z5-8448*B6)/1536,
 (3,3):(-3*pi**3*Z3+64*pi**2*B4-1581*pi*Z5+4608*B6)/1024,
 (2,4):(-14*pi**4*B2+135*pi**3*Z3-1440*pi**2*B4+23715*pi*Z5-69120*B6)/23040,
 (1,5):(-150*pi**5*lg+56*pi**4*B2-270*pi**3*Z3+1920*pi**2*B4-675*pi*Z5)/92160}

if __name__=='__main__':
    for (a,b),target in targets.items():
        got=g(a,b)
        delta=s.simplify(got-target)
        print((a,b),'g =',got,'delta =',delta)
        assert delta==0
    print('\nConstants c_ab:')
    for b in range(1,6):
        for a in range(1,7-b):
            print((a,b),constant(a,b))
