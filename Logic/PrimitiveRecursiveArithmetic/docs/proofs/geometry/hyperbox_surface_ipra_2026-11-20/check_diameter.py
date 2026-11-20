"""Independent ordered-gate checks of the long-prism theorem and CAD extraction."""
import sys
from fractions import Fraction as F
from random import Random
import sympy as sp
from free_cad import diameter, legal, on_chart, sign
from hyperbox import develop, surface_squared


def long_prism():
    # T=(10+1/10)/2 makes the analytic optimizing endpoints rational.
    height=F(101,20)
    delta=F(1,20)
    a=(F(1),)*3+(height,)
    p=(F(1,2)-delta,)*3+(0,)
    q=(F(1,2)+delta,)*3+(height,)
    expected=(height+1)**2+8*delta**2
    assert surface_squared(a,p,q)==expected==F(14649,400)
    rng=Random(29137)
    for _ in range(70):
        points=[]
        for _ in range(2):
            point=[b*F(rng.randrange(11),10) for b in a]
            wall=rng.randrange(4)
            point[wall]=a[wall]*rng.randrange(2)
            points.append(tuple(point))
        assert surface_squared(a,*points)<=expected
    print('Rational long-prism optimum and 70 other 4D boundary pairs passed.')

    # All simple cap-to-cap words on the flagship example. CRootOf keeps
    # every comparison exact in the ordered algebraic field.
    x=sp.Symbol('x')
    root=sp.CRootOf(x*x-6,1)
    a=tuple(map(sp.Integer,[1,1,1,5]))
    p=[root-2]*3+[sp.S.Zero]
    q=[3-root]*3
    exact=134-40*root
    seen=0
    equal=0
    for frame,gates in develop(a,7,{6},set()):
        site=[o+s*p[i] for i,s,o in frame]
        square=sum((x-y)**2 for x,y in zip(q,site))
        # Reduce to the basis (1,sqrt(6)) without numerical rounding.
        u=sp.Symbol('u')
        reduced=sp.rem(sp.expand((square-exact).xreplace({root:u})),u*u-6,u).subs(u,root)
        result=sign(reduced)
        if result<=0 and legal(q,site,gates):
            assert result==0
            equal+=1
        seen+=1
    assert equal>0
    assert sp.simplify(diameter((1,1,1,5))[0]-(134-40*sp.sqrt(6)))==0
    print(f'Algebraic 4D witness: {seen} simple words, {equal} valid shortest developments.')


def transition_checks():
    dim,t,u,z = sp.symbols('d t u z', positive=True)
    h0=(dim+1)/2
    base_bounds=[4+(dim-2)*(1-2*u)**2,(2-u)**2+(dim-2)*(1-u)**2]
    certificates=[(4*dim-9)*u**2+(11-3*dim)*u,
                  (dim-2)*u**2+(3-dim)*u]
    for bound,cert in zip(base_bounds,certificates):
        assert sp.expand(h0**2+bound-(h0+1-u)**2-cert)==0
    t_from_z=(z+1/z)/2
    square=(t_from_z+1)**2+(dim-1)*z**2
    corner=t_from_z**2+dim+2
    assert sp.cancel(z*(square-corner)-(z-1)*((dim-1)*z**2+dim*z-1))==0
    assert diameter([1]*5+[2])[0]==11
    assert sp.simplify(diameter([1]*5+[3])[0]-(84-48*sp.sqrt(2)))==0
    print('High-dimensional transition: polynomial certificates and both 6D branches passed.')


if __name__=='__main__':
    long_prism()
    transition_checks()
    if '--cad' in sys.argv:
        result=on_chart((sp.Integer(2),sp.Integer(3)),0,1,sp.Integer(23),sp.Integer(25))
        assert result and result[0]==25
        _,(p,q)=result
        assert surface_squared((2,3),p,q)==25
        print('Full exact projection and lifting: a rectangle chart returned 25 and attaining endpoints.')
