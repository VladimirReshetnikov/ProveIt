#!/usr/bin/env python3
"""Independent symbolic identities and high-precision checks of the Hessian.

The numerical solves are illustrations, not proof certificates. The theorem's
proof is in mirror_hessian.tex. Requires mpmath and sympy.
"""
from __future__ import annotations

import json
from pathlib import Path

import mpmath as mp
import sympy as sp

mp.mp.dps = 65
z = sp.symbols("z", real=True)
X, Y = sp.symbols("X Y", real=True)
P = 1 + z + z**2 + z**3
roots = [sp.I, -1, -sp.I]
defects = [X-sp.I*Y, -2*X, X+sp.I*Y]
S = sp.expand(sum(d*r*sp.div(P, z-r)[0] for d, r in zip(defects, roots)))
assert sp.expand(S - (2*X*(z**2-z) + 2*Y*(z**2+z))) == 0
u = [sp.Integer(0)] + [-sp.pi*S.coeff(z, k)/8 for k in (1, 2)] + [sp.Integer(0)]
Q = sp.Integer(0)
integrals = {}
for k in range(4):
    for ell in range(k+1, 4):
        integral = sp.integrate(z**(k+ell-1)/P**2, (z, 0, sp.oo))
        integrals[f"{k},{ell}"] = str(integral)
        Q += (2/sp.pi)*(u[k]-u[ell])**2*integral
expected = sp.pi*(3*X**2+(sp.pi-1)*Y**2)/16
assert sp.simplify(Q-expected) == 0


def mp_s(s):
    return mp.mpc(str(sp.N(sp.re(s), 70)), str(sp.N(sp.im(s), 70)))


def check_configuration(name, roots_exact, multiplicities, h_exact, velocity_exact, eps_strings):
    """Solve all real mass and jet equations, including repeated targets."""
    h = mp_s(h_exact).real
    target0 = [mp.log(mp_s(r))/h for r in roots_exact]
    # Principal log represents roots below the real line negatively; add 2 pi i.
    target0 = [s if s.imag > 0 else s+2*mp.pi*1j/h for s in target0]
    target0 = [mp.mpc(s.real, mp.pi/h) if abs(s.imag) < mp.mpf("1e-60") else s for s in target0]
    vs = [mp_s(v) for v in velocity_exact]
    N = sum(multiplicities)
    poly = sp.Poly(sp.expand(sp.prod((z-r)**m for r, m in zip(roots_exact, multiplicities))), z)
    coefficients = [mp_s(poly.nth(k)).real for k in range(N+1)]
    assert all(p > 0 for p in coefficients)
    weights = [p/sum(coefficients) for p in coefficients]
    T = 2*mp.pi/h
    pairing = [next(j for j, r2 in enumerate(roots_exact) if sp.simplify(r2-sp.conjugate(r)) == 0) for r in roots_exact]
    assert abs(sum(m*v.imag for m,v in zip(multiplicities,vs))) < mp.mpf("1e-60")
    d = [(vs[j]-mp.conj(vs[pairing[j]]))/1j for j in range(len(vs))]
    Ucoeff = [mp.mpf(0)]*(N+1)
    for j, (r, m) in enumerate(zip(roots_exact,multiplicities)):
        quot = sp.Poly(sp.div(poly.as_expr(), z-r)[0], z)
        for k in range(N):
            Ucoeff[k] += -h/T/sum(coefficients)*m*d[j]*mp_s(r)*mp_s(quot.nth(k))
    velocities = [mp.re(Ucoeff[k])/weights[k] for k in range(N+1)]
    assert max(abs(mp.im(c)) for c in Ucoeff) < mp.mpf("1e-60")
    assert abs(velocities[0])+abs(velocities[-1]) < mp.mpf("1e-60")

    def polynomial(y):
        return sum(coefficients[k]*y**k for k in range(N+1))

    predicted = mp.mpf(0)
    for k in range(N+1):
        for ell in range(k+1,N+1):
            integral = mp.quad(lambda y: y**(k+ell-1)/polynomial(y)**2, [0,1,mp.inf])
            predicted += coefficients[k]*coefficients[ell]*(velocities[k]-velocities[ell])**2*integral/h

    initial = tuple(weights) + tuple(h*k for k in range(1,N+1))
    def solve(eps):
        targets = [s+eps*v for s,v in zip(target0,vs)]
        def equations(*values):
            ws = values[:N+1]
            ts = (mp.mpf(0),)+values[N+1:]
            ans = [sum(ws)-1]
            for sj,m in zip(targets,multiplicities):
                for derivative in range(m):
                    moment = sum(w*t**derivative*mp.exp(sj*t) for w,t in zip(ws,ts))
                    ans.extend([mp.re(moment),mp.im(moment)])
            return tuple(ans)
        sol = list(mp.findroot(equations, initial, tol=mp.mpf("1e-55"), maxsteps=80, verify=True))
        residual = max(abs(t) for t in equations(*sol))
        assert min(sol[:N+1]) > 0
        nodes = [mp.mpf(0)]+list(sol[N+1:])
        assert all(a<b for a,b in zip(nodes,nodes[1:]))
        return sol, residual

    checks = []
    for eps_string in eps_strings:
        eps = mp.mpf(eps_string)
        plus,rp = solve(eps)
        minus,rm = solve(-eps)
        symmetric = (plus[-1]+minus[-1]-2*N*h)/(2*eps**2)
        observed_node_velocities = [(plus[N+1+k-1]-minus[N+1+k-1])/(2*eps) for k in range(1,N+1)]
        checks.append({
            "epsilon": eps_string,
            "predicted_quadratic_coefficient": mp.nstr(predicted,35),
            "symmetric_observed_coefficient": mp.nstr(symmetric,35),
            "absolute_coefficient_error": mp.nstr(abs(symmetric-predicted),15),
            "max_node_velocity_error": mp.nstr(max(abs(observed_node_velocities[k-1]-velocities[k]) for k in range(1,N+1)),15),
            "max_equation_residual": mp.nstr(max(rp,rm),8),
        })
    assert mp.mpf(checks[-1]["absolute_coefficient_error"]) < mp.mpf("1e-7")
    return {"name":name,"total_multiplicity":N,"roots":[str(r) for r in roots_exact],
            "multiplicities":multiplicities,"h":str(h_exact),"velocity":[str(v) for v in velocity_exact],
            "checks":checks}


cases = [
    check_configuration("three_modes_mixed", [sp.I,-1,-sp.I], [1,1,1], sp.pi/2,
                        [sp.Rational(2,5)+sp.I*sp.Rational(3,10),-sp.Rational(1,10)-sp.I*sp.Rational(4,5),
                         -sp.Rational(7,10)+sp.I/2], ["0.001","0.0001","0.00001"]),
    check_configuration("repeated_targets", [sp.I,-1,-sp.I], [2,1,2], sp.pi/2,
                        [1+sp.I,-4*sp.I,-1+sp.I], ["0.0001","0.00001"]),
    check_configuration("unequal_base_real_parts", [2*sp.I,-3,-2*sp.I], [1,1,1], sp.Integer(1),
                        [sp.Rational(1,3)+sp.I,sp.Rational(1,2)-2*sp.I,-sp.Rational(2,3)+sp.I],
                        ["0.0001","0.00001"]),
]
result={"symbolic_identity_passed":True,"three_mode_hessian":str(expected),
        "exact_integrals":integrals,"numeric_checks_are_proofs":False,"precision_digits":mp.mp.dps,"cases":cases}
out=Path(__file__).with_name("mirror_hessian_checks.json")
out.write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result,indent=2))
