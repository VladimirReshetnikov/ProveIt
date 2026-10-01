"""Exact positive hyperbolic-rail and nonexplosive mass-action lifts."""
from __future__ import annotations
from dataclasses import dataclass
import sympy as sp


@dataclass
class Lift:
    original_variables: tuple
    original_field: tuple
    rails: tuple
    rail_field: tuple
    species: tuple
    field: tuple
    clock_factor: sp.Expr
    degree_bound: int
    damping_power: int

    def reactions(self) -> list[dict]:
        """Canonical one-coordinate reaction for each collected monomial."""
        result = []
        for i, expression in enumerate(self.field):
            for alpha, coefficient in sp.Poly(expression, *self.species).terms():
                if not coefficient:
                    continue
                if not coefficient.is_Rational:
                    raise ValueError("only rational coefficients supported")
                beta = list(alpha)
                if coefficient > 0:
                    beta[i] += 1
                else:
                    if alpha[i] == 0:
                        raise ValueError("nonkinetic negative monomial")
                    beta[i] -= 1
                result.append({"reactants": list(alpha), "products": beta,
                               "rate": str(abs(coefficient)), "coordinate": i})
        return result


def build_lift(variables: tuple, field: tuple) -> Lift:
    if not variables or len(variables) != len(field):
        raise ValueError("nonempty matching dimensions required")
    d = len(variables)
    polys = [sp.Poly(f, *variables, domain=sp.QQ) for f in field]
    k = max([1] + [max(0, int(p.total_degree())) for p in polys if not p.is_zero])
    p = sp.symbols(f"p0:{d}")
    n = sp.symbols(f"n0:{d}")
    y = p + n
    substitution = {x: pp - nn for x, pp, nn in zip(variables, p, n)}
    fs = [f.as_expr().subs(substitution, simultaneous=True) for f in polys]
    c = sp.prod(pp + nn for pp, nn in zip(p, n))
    cj = [sp.prod(p[i] + n[i] for i in range(d) if i != j) for j in range(d)]
    g = tuple(sp.expand(p[j] * cj[j] * fs[j]) for j in range(d)) + \
        tuple(sp.expand(-n[j] * cj[j] * fs[j]) for j in range(d))
    upper = k + d
    s = (upper + 1) // 2
    q = sp.Symbol("q")
    dot = sum(a * b for a, b in zip(y, g))
    full = tuple(sp.expand(q**s * f) for f in g) + (sp.expand(-2*q**(s+2)*dot),)
    return Lift(variables, field, y, g, y+(q,), full,
                sp.expand(q**s*c), upper+s+3, s)


def check_lift(lift: Lift) -> dict:
    d = len(lift.original_variables)
    p, n = lift.rails[:d], lift.rails[d:]
    g, y = lift.rail_field, lift.rails
    q = lift.species[-1]
    c = sp.prod(pp+nn for pp, nn in zip(p, n))
    subs = {x: pp-nn for x, pp, nn in zip(lift.original_variables, p, n)}
    for j in range(d):
        assert sp.expand(n[j]*g[j] + p[j]*g[d+j]) == 0
        assert sp.expand(g[j]-g[d+j]-c*lift.original_field[j].subs(subs, simultaneous=True)) == 0
    invariant = q*(1+sum(a*a for a in y))-1
    derivative = sp.expand(sum(sp.diff(invariant, a)*b
                               for a, b in zip(lift.species, lift.field)))
    dot = sum(a*b for a, b in zip(y, g))
    assert sp.expand(derivative + 2*q**(lift.damping_power+1)*dot*invariant) == 0
    reactions = lift.reactions()
    reconstructed = [sp.Integer(0) for _ in lift.species]
    for reaction in reactions:
        monomial = sp.Rational(reaction["rate"]) * sp.prod(
            a**e for a, e in zip(lift.species, reaction["reactants"]))
        for i in range(len(lift.species)):
            reconstructed[i] += (reaction["products"][i]-reaction["reactants"][i])*monomial
    assert all(sp.expand(a-b) == 0 for a, b in zip(reconstructed, lift.field))
    actual_degree = max([0] + [int(sp.Poly(f, *lift.species).total_degree())
                              for f in lift.field if f != 0])
    assert actual_degree <= lift.degree_bound
    return {"dimension": d, "species": len(lift.species),
            "reaction_count": len(reactions), "actual_degree": actual_degree,
            "degree_bound": lift.degree_bound, "damping_power": lift.damping_power,
            "rail_invariants": True, "projection_identity": True,
            "damping_invariant": True, "kinetic_sign_condition": True,
            "reaction_reconstruction": True}


def build_offset_lift(variables: tuple, field: tuple) -> Lift:
    """Compress to d+2 species, trading three units in the degree upper bound."""
    if not variables or len(variables) != len(field):
        raise ValueError("nonempty matching dimensions required")
    d = len(variables)
    polys = [sp.Poly(f, *variables, domain=sp.QQ) for f in field]
    k = max([1] + [max(0, int(p.total_degree())) for p in polys if not p.is_zero])
    u = sp.symbols(f"u0:{d}")
    z, q = sp.symbols("z q")
    y = u + (z,)
    xs = tuple(a-z for a in u)
    subs = dict(zip(variables, xs))
    fs = [p.as_expr().subs(subs, simultaneous=True) for p in polys]
    a = sum(x*f for x,f in zip(xs, fs))
    product = sp.prod(u)
    g = tuple(sp.expand(z*product*(z*f+a)) for f in fs) + (sp.expand(z*product*a),)
    upper = k+d+2
    power = (upper+1)//2
    dot = sum(a*b for a,b in zip(y,g))
    full = tuple(sp.expand(q**power*f) for f in g) + (sp.expand(-2*q**(power+2)*dot),)
    return Lift(variables, tuple(p.as_expr() for p in polys), y, g,
                y+(q,), full, sp.expand(q**power*z*z*product), upper+power+3, power)


def check_offset_lift(lift: Lift) -> dict:
    d = len(lift.original_variables)
    u, z = lift.rails[:d], lift.rails[-1]
    q = lift.species[-1]
    y, g = lift.rails, lift.rail_field
    xs = tuple(a-z for a in u)
    product = sp.prod(u)
    subs = dict(zip(lift.original_variables, xs))
    invariant = z*z-sum(a*a for a in xs)
    assert sp.expand(sum(sp.diff(invariant,a)*b for a,b in zip(y,g))) == 0
    for i in range(d):
        assert sp.expand(g[i]-g[-1]-z*z*product*
                         lift.original_field[i].subs(subs, simultaneous=True)) == 0
    damping = q*(1+sum(a*a for a in y))-1
    derivative = sum(sp.diff(damping,a)*b for a,b in zip(lift.species,lift.field))
    dot = sum(a*b for a,b in zip(y,g))
    assert sp.expand(derivative+2*q**(lift.damping_power+1)*dot*damping) == 0
    reactions = lift.reactions()
    reconstructed = [sp.Integer(0) for _ in lift.species]
    for reaction in reactions:
        monomial = sp.Rational(reaction['rate'])*sp.prod(
            a**e for a,e in zip(lift.species,reaction['reactants']))
        for i in range(len(lift.species)):
            reconstructed[i] += (reaction['products'][i]-reaction['reactants'][i])*monomial
    assert all(sp.expand(a-b) == 0 for a,b in zip(lift.field,reconstructed))
    degree = max([0]+[int(sp.Poly(f,*lift.species).total_degree()) for f in lift.field if f != 0])
    assert degree <= lift.degree_bound
    return {'dimension':d, 'species':len(lift.species),
            'reaction_count':len(reactions), 'actual_degree':degree,
            'degree_bound':lift.degree_bound, 'offset_invariant':True,
            'projection_identity':True, 'damping_invariant':True,
            'kinetic_sign_condition':True, 'reaction_reconstruction':True}
