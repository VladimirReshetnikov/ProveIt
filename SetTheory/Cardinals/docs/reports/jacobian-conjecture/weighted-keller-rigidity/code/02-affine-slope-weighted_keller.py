"""Exact recognition of rational affine-in-v weighted Keller maps.

Coordinates: t = x*y, v = x**2*z; lift(p,q,r)=(p/x**2,q/x,x*r).
The classifier uses the normal-form theorem, not a degree-limited search.
Only rational coefficients are accepted by this executable implementation.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Literal
import sympy as sp

t, v = sp.symbols('t v')
x, y, z = sp.symbols('x y z')

@dataclass(frozen=True)
class Classification:
    kind: Literal['not-keller', 'tame', 'noninjective']
    reason: str
    normalized: tuple[sp.Expr, sp.Expr, sp.Expr] | None = None
    output_scales: tuple[sp.Rational, sp.Rational, sp.Rational] | None = None
    parameters: dict[str, Any] | None = None


def _poly(expr: Any) -> sp.Poly:
    try:
        return sp.Poly(sp.sympify(expr), t, v, domain=sp.QQ)
    except (sp.PolynomialError, sp.CoercionFailed, TypeError, ValueError) as exc:
        raise ValueError('Expected a polynomial in t,v with rational coefficients.') from exc


def weighted_jacobian(p: Any, q: Any, r: Any) -> sp.Expr:
    p, q, r = map(sp.sympify, (p, q, r))
    return sp.expand(sp.det(sp.Matrix([
        [-2*p, sp.diff(p,t), sp.diff(p,v)],
        [-q, sp.diff(q,t), sp.diff(q,v)],
        [r, sp.diff(r,t), sp.diff(r,v)]])))


def lift(p: Any, q: Any, r: Any) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    """Return the three polynomial coordinates, or raise ValueError."""
    polys = [_poly(w).as_expr() for w in (p,q,r)]
    substitution = {t:x*y, v:x*x*z}
    result = tuple(sp.cancel(w.subs(substitution) * factor)
                   for w,factor in zip(polys, (x**-2,x**-1,x)))
    try:
        return tuple(sp.Poly(w,x,y,z,domain=sp.QQ).as_expr() for w in result)
    except sp.PolynomialError as exc:
        raise ValueError('The proposed invariant numerators do not lift polynomially.') from exc


def normal_form(beta: Any, gamma: Any, R: Any) -> tuple[sp.Expr, sp.Expr, sp.Expr]:
    beta, gamma = sp.Rational(beta), sp.Rational(gamma)
    if beta == 0 or gamma == 0:
        raise ValueError('beta and gamma must be nonzero rational numbers.')
    R = sp.Poly(R,t,domain=sp.QQ).as_expr()
    if R.subs(t,0) != 1 or sp.diff(R,t).subs(t,0) != beta:
        raise ValueError("R must satisfy R(0)=1 and R'(0)=beta.")
    U, S = 1-sp.Rational(2,3)*beta*t, R+gamma*v
    return tuple(map(sp.expand, (
        (U**3*S-(U**2+U)/2)/gamma,
        9/beta*(U**2*S-(2*U+1)/3), S)))


def classify(p: Any, q: Any, r: Any) -> Classification:
    polys = tuple(_poly(w) for w in (p,q,r))
    if any(w.degree(v) > 1 for w in polys):
        raise ValueError('Outside the theorem: each numerator must be affine in v.')
    p,q,r = (w.as_expr() for w in polys)
    a,b = sp.diff(p,v),p.subs(v,0)
    c,d = sp.diff(q,v),q.subs(v,0)
    g,e = sp.diff(r,v),r.subs(v,0)
    if b.subs(t,0)!=0 or sp.diff(b,t).subs(t,0)!=0 or d.subs(t,0)!=0:
        raise ValueError('Polynomiality requires b(0)=b\'(0)=d(0)=0.')
    scales = (a.subs(t,0),sp.diff(d,t).subs(t,0),e.subs(t,0))
    if any(w==0 for w in scales):
        return Classification('not-keller','The Jacobian vanishes at the origin.')
    pn,qn,rn = tuple(sp.expand(w/s) for w,s in zip((p,q,r),scales))
    a,b = sp.diff(pn,v),pn.subs(v,0)
    c,d = sp.diff(qn,v),qn.subs(v,0)
    g,e = sp.diff(rn,v),rn.subs(v,0)
    normalized=(pn,qn,rn)
    def no(reason: str) -> Classification:
        return Classification('not-keller',reason,normalized,scales)
    if sp.diff(g,t)!=0:
        return no('The third invariant slope is nonconstant.')
    if g==0:
        lam=c.subs(t,0)
        expected=(v+b,t+lam*(v+b),sp.Integer(1))
        if any(sp.expand(w-h)!=0 for w,h in zip(normalized,expected)):
            return no('The zero-slope branch fails the tame normal-form identities.')
        return Classification('tame','Exact tame normal form.',normalized,scales,
                              {'lambda':lam,'B':b,'H':sp.cancel(b/t**2)})
    beta=sp.diff(e,t).subs(t,0)
    if beta==0:
        return no('A nonzero third slope requires R\'(0) != 0.')
    expected=normal_form(beta,g,e)
    if any(sp.expand(w-h)!=0 for w,h in zip(normalized,expected)):
        return no('The nonzero-slope branch fails the normal-form identities.')
    h=sp.cancel((e-1-beta*t)/(g*t*t))
    return Classification('noninjective','Exact noninjective normal form.',normalized,scales,
                          {'beta':beta,'gamma':g,'R':e,'h':h})


def normalized_collision(result: Classification) -> tuple[tuple[sp.Expr,...],tuple[sp.Expr,...]]:
    """The same source points collide before or after output normalization."""
    if result.kind!='noninjective' or result.parameters is None:
        raise ValueError('A noninjective classification is required.')
    beta=result.parameters['beta']; gamma=result.parameters['gamma']; h=result.parameters['h']
    return ((sp.Integer(1),sp.Integer(0),-1/gamma),
            (sp.Integer(0),-9/beta,71/gamma-81*h.subs(t,0)/beta**2))


def infinitesimal_direction(G: Any) -> tuple[sp.Expr,sp.Expr]:
    """Return C and the second-order obstruction for a rational polynomial G."""
    G=sp.Poly(G,t,domain=sp.QQ).as_expr()
    C=sp.expand(-t*G-2*sp.integrate(G,(t,0,t)))
    obstruction=sp.expand(C*sp.diff(G,t)-3*G*sp.diff(C,t))
    return C,obstruction

if __name__=='__main__':
    p,q,r=normal_form(1,1,1+t+t**2*(1+t))
    result=classify(p,q,r)
    print(result)
    print('Colliding source points:',normalized_collision(result))
