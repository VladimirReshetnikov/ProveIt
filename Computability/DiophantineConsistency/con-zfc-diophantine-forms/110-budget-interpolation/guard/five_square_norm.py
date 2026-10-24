"""Division-free five-radical norm over an arbitrary commutative ring.

Inputs may be integers, sparse polynomials, or arithmetic-DAG registers.
No square roots, divisions, variable powers, or branches enter the output.
"""

def _square_biquadratic(t,d,e):
    """Square t0+t1*u+t2*v+t3*u*v, with u^2=d and v^2=e."""
    a,b,c,f=t
    return (a*a+d*(b*b)+e*(c*c)+d*e*(f*f),
            2*(a*b+e*c*f),
            2*(a*c+d*b*f),
            2*(a*f+b*c))

def five_square_norm(x,a,b,c,d,e):
    """Product of x-eps1*sqrt(a)-...-eps5*sqrt(e) over all 32 signs."""
    s=a+b+c
    p=a*b+a*c+b*c
    abc64=64*a*b*c
    # t=x-u-v.  Its square is stored directly, not by four-component mul.
    t2=(x*x+d+e,-2*x,-2*x,2)
    shifted=(t2[0]-s,t2[1],t2[2],t2[3])
    first=_square_biquadratic(shifted,d,e)
    first=(first[0]-4*p,first[1],first[2],first[3])
    second=_square_biquadratic(first,d,e)
    f=tuple(second[i]-abc64*t2[i] for i in range(4))
    # Norm first over u, then over v.
    g0=f[0]*f[0]+e*f[2]*f[2]-d*(f[1]*f[1]+e*f[3]*f[3])
    g1=2*(f[0]*f[2]-d*f[1]*f[3])
    return g0*g0-e*g1*g1

def three_square_norm(x,a,b,c):
    q=x*x-(a+b+c)
    t=q*q-4*(a*b+a*c+b*c)
    return t*t-64*a*b*c*x*x

def four_square_norm(x,a,b,c,d):
    """Four-radical companion via a quadratic extension."""
    # F8(x-u;a,b,c), u^2=d. q=(x-u)^2-(a+b+c)=q0+q1*u.
    q0=x*x+d-a-b-c;q1=-2*x
    t0=q0*q0+d*q1*q1-4*(a*b+a*c+b*c)
    t1=2*q0*q1
    z=64*a*b*c
    f0=t0*t0+d*t1*t1-z*(x*x+d)
    f1=2*t0*t1+2*z*x
    return f0*f0-d*f1*f1

# Short public names requested by the integrating builder.
norm3=three_square_norm
norm4=four_square_norm
norm5=five_square_norm

def cleared_norm5(x,a,b,c,d,cn,delta):
    """delta^16 F32(x;a,b,c,d,cn/delta), as an ordinary polynomial.

    The identity is polynomial after clearing the denominator; delta need
    not be nonzero for evaluating this expression. Applications using its
    rational interpretation must separately prove delta != 0.
    """
    # Put the rational radicand in the innermost three-root norm.
    # t=x-u-v, u^2=c, v^2=d.
    t2=(x*x+c+d,-2*x,-2*x,2)
    q=(delta*(t2[0]-a-b)-cn,delta*t2[1],delta*t2[2],delta*t2[3])
    tn=delta*delta*a*b
    rn=delta*cn
    z64=64*tn*rn
    first=_square_biquadratic(q,c,d)
    first=(first[0]-4*(tn+rn*(a+b)),first[1],first[2],first[3])
    second=_square_biquadratic(first,c,d)
    f=tuple(second[i]-z64*t2[i] for i in range(4))
    g0=f[0]*f[0]+d*f[2]*f[2]-c*(f[1]*f[1]+d*f[3]*f[3])
    g1=2*(f[0]*f[2]-c*f[1]*f[3])
    return g0*g0-d*g1*g1

norm5_cleared=cleared_norm5

def cleared_norm5_scaled(x,a,b,c,d,C,delta):
    """Alternative denominator scaling proposed by the integrating author."""
    s=a+b+c;p=a*b+a*c+b*c;K=64*a*b*c
    u=delta*(x*x+d-s)+C
    t0=delta*(x*x+d)+C
    A0=u*u+4*delta*delta*d*x*x+4*delta*C*x*x+4*delta*C*d-4*delta*delta*p
    A1=-4*x*(u+2*C)
    A2=-4*x*(u+2*delta*d)
    A3=4*(u+2*delta*x*x)
    f0=A0*A0+d*delta*delta*A1*A1+C*delta*A2*A2+d*C*delta*A3*A3-K*delta*delta*delta*t0
    f1=2*(A0*A1+C*A2*A3)+2*K*delta*delta*delta*x
    f2=2*(A0*A2+d*delta*A1*A3)+2*K*delta*delta*delta*x
    f3=2*(A0*A3+delta*A1*A2)-2*K*delta*delta*delta
    g0=f0*f0+C*delta*f2*f2-d*delta*delta*f1*f1-d*C*delta*f3*f3
    g1=2*(f0*f2-d*delta*f1*f3)
    return g0*g0-C*delta*g1*g1

def cleared_norm5_compact(x,a,b,c,d,cn,delta):
    """Same polynomial, factoring the duplicated first-stage components."""
    x2=x*x;cdsum=c+d;absum=a+b;ab=a*b
    delta2=delta*delta
    j=delta*(x2+cdsum-absum)-cn
    rn=delta*cn
    four_delta=4*delta
    two_delta=2*delta
    K0=j*j+4*delta2*(cdsum*x2+c*d-ab)-4*rn*absum
    neg_four_delta_x=-(four_delta*x)
    K1=neg_four_delta_x*(j+two_delta*d)
    K2=neg_four_delta_x*(j+two_delta*c)
    K3=four_delta*(j+two_delta*x2)
    second=_square_biquadratic((K0,K1,K2,K3),c,d)
    z64=64*delta2*ab*rn
    t2=(x2+cdsum,-2*x,-2*x,2)
    f=tuple(second[i]-z64*t2[i] for i in range(4))
    g0=f[0]*f[0]+d*f[2]*f[2]-c*(f[1]*f[1]+d*f[3]*f[3])
    g1=2*(f[0]*f[2]-c*f[1]*f[3])
    return g0*g0-d*g1*g1

def cleared_norm5_compact2(x,a,b,c,d,cn,delta):
    """Fully factored first-stage and even second-stage components."""
    x2=x*x;cdsum=c+d;absum=a+b;ab=a*b
    delta2=delta*delta
    j=delta*(x2+cdsum-absum)-cn
    rn=delta*cn
    four_delta=4*delta;two_delta=2*delta
    K0=j*j+four_delta*(delta*(cdsum*x2+c*d-ab)-cn*absum)
    four_delta_x=four_delta*x
    K1=four_delta_x*(j+two_delta*d)
    K2=four_delta_x*(j+two_delta*c)
    K3=four_delta*(j+two_delta*x2)
    z64=64*delta2*ab*rn
    z64x=z64*x
    f0=K0*K0+c*(K1*K1)+d*(K2*K2)+c*d*(K3*K3)-z64*(x2+cdsum)
    f1=K0*K1+d*K2*K3-z64x
    f2=K0*K2+c*K1*K3-z64x
    f3=K0*K3+K1*K2-z64
    g0=f0*f0+4*(d*f2*f2-c*(f1*f1+d*f3*f3))
    g1=f0*f2-2*c*f1*f3
    return g0*g0-16*d*g1*g1
