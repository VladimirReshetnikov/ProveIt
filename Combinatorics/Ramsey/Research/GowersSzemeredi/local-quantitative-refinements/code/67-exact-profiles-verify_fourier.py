#!/usr/bin/env python3
"""Independent numerical diagnostics for the written Fourier-gap theorems.

The proofs in the article establish the general results. Floating-point
matrix, root, moment, and grid-LP checks here are diagnostics, not proofs.
An exact SymPy identity verifies the rational R=3 example separately.
"""
from pathlib import Path
import json
import math
import numpy as np
from scipy.linalg import null_space
from scipy.optimize import linprog
import sympy as sp


def matrices(c, eps):
    r = len(eps)
    h = np.r_[1.0, -np.asarray(eps)]
    moment = np.array([[h[abs(i-j)] for j in range(r+1)]
                       for i in range(r+1)])
    loc = np.array([[c*h[abs(i-j)]
                     - (h[abs(i-j+1)]+h[abs(i-j-1)])/2
                     for j in range(r)] for i in range(r)])
    return moment, loc


def solve_branch(a, eps):
    c = math.cos(a)
    moment, loc = matrices(c, eps)
    r = len(eps)
    e = np.ones(r)
    raw = np.linalg.solve(loc, e)
    beta = e @ raw
    weights = raw/beta
    s = -1/((1-c)*beta)
    ac = [float(weights[:r-j] @ weights[j:]) for j in range(r)] + [0., 0.]
    coeff = [(ac[1]-c*ac[0])/(1-c)]
    for j in range(1, r+1):
        coeff.append(((ac[j-1]+ac[j+1])/2-c*ac[j])/(1-c))
    z = null_space(e[None, :])
    mineig_z = float(np.linalg.eigvalsh(z.T @ loc @ z).min()) if r > 1 else 1.
    mineig_m = float(np.linalg.eigvalsh(moment-s*np.ones((r+1, r+1))).min())
    assert beta < 0 and 0 < s < 1 and mineig_z > 0 and mineig_m > 0
    assert min(coeff[1:]) > 0
    roots = np.roots(weights[::-1])
    assert max([abs(abs(x)-1) for x in roots] or [0.]) < 2e-7
    angles = np.r_[0., -a, a, np.angle(roots)]
    vand = np.exp(-1j*np.outer(np.arange(-r, r+1), angles))
    target = np.r_[-np.asarray(eps)[::-1], 1., -np.asarray(eps)]
    masses = np.linalg.lstsq(np.r_[vand.real, vand.imag],
                             np.r_[target, np.zeros(2*r+1)], rcond=None)[0]
    err = float(np.max(np.abs(vand @ masses-target)))
    assert err < 5e-9 and masses.min() > 0 and abs(masses[0]-s) < 5e-9
    return {'s': s, 'w': weights, 'coeff': coeff, 'angles': angles,
            'masses': masses, 'moment_error': err, 'mineig_z': mineig_z,
            'mineig_m': mineig_m}


def main():
    rng = np.random.default_rng(20261007)
    diagnostics = []
    max_error = 0.
    for r in range(1, 11):
        for factor in (1.20, 1.45, 1.75):
            a = factor*math.pi/(r+1)
            rho = 1/(r - math.tan((r+1)*a/2)/math.tan(a/2))
            for trial in range(4):
                eps = rho*(.45+0.001*rng.uniform(-1, 1, r))
                result = solve_branch(a, eps)
                max_error = max(max_error, result['moment_error'])
                diagnostics.append((r, factor, trial))

    t = sp.symbols('t')
    formula = sp.Rational(338, 3)/(91+12*t)-sp.Rational(7, 6)
    frozen = sp.Rational(1, 14)-8*t/49
    assert sp.cancel(formula-frozen-96*t*t/(49*(91+12*t))) == 0
    # Construct the exact localizing matrix independently from its definition.
    eps_symbolic = [sp.Rational(1, 12), sp.Rational(1, 12), sp.Rational(1, 12)+t]
    h = [sp.Integer(1)]+[-x for x in eps_symbolic]
    loc = sp.Matrix(3, 3, lambda i,j: h[abs(i-j)]/2
                    -(h[abs(i-j+1)]+h[abs(i-j-1)])/2)
    beta = (sp.ones(1,3)*loc.inv()*sp.ones(3,1))[0]
    assert sp.cancel(-2/beta-formula) == 0

    lp_checks = []
    for t_value in (-.01, -.005, 0., .005, .01):
        a = math.pi/3
        eps = np.array([1/12, 1/12, 1/12+t_value])
        branch = solve_branch(a, eps)
        # Reflection-symmetric LP on [0,pi], not on the theorem's exact support.
        theta = np.unique(np.r_[np.linspace(0, math.pi, 2401), a])
        cosine = np.cos(np.outer(np.arange(1, 4), theta))
        cost = (theta < a-1e-12).astype(float)
        lp = linprog(cost, A_ub=np.r_[cosine, -cosine],
                     b_ub=np.r_[eps, eps], A_eq=np.ones((1,len(theta))),
                     b_eq=[1.], bounds=(0,None), method='highs')
        assert lp.success
        excess = float(lp.fun-branch['s'])
        assert excess > -1e-8 and excess < 2e-6
        lp_checks.append({'t':t_value, 'exact_branch':branch['s'],
                          'grid_LP':float(lp.fun), 'grid_excess':excess})

    grid_checks = []
    for r in (2,3,5):
        a = 1.4*math.pi/(r+1)
        for n in (101,211,431):
            step = 2*math.pi/n
            a_grid = math.ceil(a/step)*step
            theta = np.arange(n)*step
            allowed = np.minimum(theta, 2*math.pi-theta) >= a-1e-12
            theta = theta[allowed]
            cosine = np.cos(np.outer(np.arange(1,r+1),theta))
            # Symmetry can be imposed implicitly: averaging any solution
            # cancels sine moments without changing its cosine constraints.
            aub = np.r_[np.c_[cosine,-np.ones(r)],
                         np.c_[-cosine,-np.ones(r)]]
            obj = np.r_[np.zeros(len(theta)),1.]
            lp = linprog(obj, A_ub=aub, b_ub=np.zeros(2*r),
                         A_eq=np.r_[np.ones(len(theta)),0.][None,:],
                         b_eq=[1.], bounds=(0,None), method='highs')
            assert lp.success
            rho = 1/(r-math.tan((r+1)*a_grid/2)/math.tan(a_grid/2))
            bound = math.pi**2*r*r/(2*n*n)
            excess = float(lp.fun-rho)
            assert excess > -1e-8 and excess <= bound+1e-8
            grid_checks.append({'R':r,'N':n,'optimum':float(lp.fun),
                                'comparison':rho,'excess':excess,'bound':bound})

    output = {'scope':'Exact symbolic identities plus floating-point diagnostics; '
                     'general proofs are in the article.',
              'branch_cases':len(diagnostics), 'max_moment_residual':max_error,
              'rational_identities':'passed', 'unequal_budget_LP':lp_checks,
              'finite_grid_LP':grid_checks}
    path = Path(__file__).with_name('fourier_results.json')
    path.write_text(json.dumps(output, indent=2)+'\n')
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
