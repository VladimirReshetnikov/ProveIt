"""Exact positive auxiliary sign classification for the unchanged86 candidate.

The full negative-input criterion is conditional on fixed actual first/main
and outer transport data.  No passing full outer tuple or false-input zero
is asserted by this packet.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import comb
from pathlib import Path
import random

import complete75_weakened86_negative_input_residues as residues
import complete75_weakened_bound86_candidate as candidate

pell, pell_mod = residues.pell, residues.pell_mod
FIELDS = ('f', 'i', 'j', 'o', 'y_aux')
PORTS = ('A', 'R10a', 'index_difference')


def allowed_signs(p):
    assert p >= 3 and p % 2
    return (-1,) if p % 4 == 1 else (-1, 1)


def canonical_recipe(A, p, omega):
    """Indices only: this does not materialize enormous Pell coordinates."""
    assert A >= 3 and omega in allowed_signs(p)
    c = pell(A, p)[1]
    if p % 4 == 3:
        m = c*p
        ell = p if omega == 1 else p+2*m
    else:
        m = 2*c*p
        ell = p+2*m
    return dict(A=A, p=p, c=c, omega=omega, m=m, ell_base=ell, ell_step=4*m,
        f='chi_A(m)', i='psi_A(m)/c^2', T='(A^2-1)*psi_A(m)',
        V='chi_T(ell)/T', y_aux='psi_T(ell)', j='(V+target)/c', o='(V+c)/f')


def aux_rows():
    """Extract the literal three-factor source with its actual open ports."""
    source = candidate.sources()[3]
    nodes = {n: (op, a, b) for n, op, a, b in source}
    done, rows = set(FIELDS+PORTS), []
    def visit(value):
        if isinstance(value, int) or value in done:
            return
        op, a, b = nodes[value]
        visit(a)
        visit(b)
        rows.append((value, op, a, b))
        done.add(value)
    for output in ('norm_strong', 'norm_aux', 'norm_linear'):
        visit(output)
    return rows


def run_aux(A, c, target, lam, values):
    env = dict(values, A=A*A-1, R10a=c, index_difference=target+lam)
    for name, op, a, b in aux_rows():
        x, y = (env[v] if isinstance(v, str) else v for v in (a, b))
        env[name] = x+y if op == '+' else x-y if op == '-' else x*y
    return env


def materialize(A, p, target, omega, ell_steps=0, bit_limit=1000000):
    """Small-host literal positive lift; guarded against huge Pell output."""
    assert (target-omega*p) % pell(A, p)[1] == 0 and ell_steps >= 0
    recipe = canonical_recipe(A, p, omega)
    c, m = recipe['c'], recipe['m']
    # chi_A(m)<(2A)^m bounds both strong coordinates before construction.
    assert m*(2*A).bit_length() <= bit_limit, 'strong witness exceeds audit budget'
    f, t = pell(A, m)
    assert t % (c*c) == 0
    i, T = t//(c*c), (A*A-1)*t
    ell = recipe['ell_base']+ell_steps*recipe['ell_step']
    while True:
        assert ell*(2*T).bit_length() <= bit_limit, 'auxiliary witness exceeds audit budget'
        chi, y = pell(T, ell)
        assert chi % T == 0
        V = chi//T
        if V+target > 0:
            break
        ell += recipe['ell_step']
    assert (V+c) % f == 0 and (V+target) % c == 0
    result = dict(f=f, i=i, j=(V+target)//c, o=(V+c)//f, y_aux=y)
    assert min(result.values()) > 0
    for lam in (-1, 1):
        actual = run_aux(A, c, target, lam, result)
        assert actual['norm_strong'] == actual['norm_aux'] == 1
        assert actual['norm_linear'] == lam
        assert actual['aux_u_rhs'] == V
    return result, dict(A=A, p=p, omega=omega, target=target, m=m, ell=ell,
        f_bits=f.bit_length(), auxiliary_root_bits=V.bit_length(),
        all_five_supplied_coordinates_positive=True)


def outer_contract(data):
    """Check fixed compiler, first/main Pell, ratio and transport data."""
    d, J, x = (data[n] for n in ('cell_bits', 'Jrep', 'x'))
    assert d >= 4 and min(J, x, data['F'], data['alpha'], data['w'], data['s'], data['zplus']) > 0
    B, q = 1 << d, ((1 << d)-1)*J+1
    assert data['B'] == B and 0 < data['inner_bits'] < B
    MC, MF = data['MC'], data['MF']
    assert 0 < MC < B-1 and 0 < MF < B-1 and MC % 4 == 2 and MF % 8 == 4
    assert MC.bit_count()+MF.bit_count() == d
    K0 = data['DC']+B*data['DR']
    assert K0 > 0
    n, p = data['n'], data['p']
    assert p >= 13 and p % 2 and n < p < 2*n
    X, Y = data['w']*q**3, data['s']*q**3
    E, a = X*Y, Y*(X+1)
    A, H = a+2, 4*a+3
    main, c = pell(A, p)
    first, first_y = pell(2*X*Y*Y+1, n)
    k = 2*first_y
    eta, zeta = c-k*Y, k-(c-k*Y)
    tau_gap = first-X*Y*Y*k
    assert min(eta, zeta, tau_gap) > 0
    quotient, remainder = divmod(main-a*c-X, H)
    assert remainder == 0 and quotient >= 2
    C = q-data['F']-data['alpha']-2*d*x
    assert C >= 0
    nu = (K0+X)*C+(q-data['F'])-data['zplus']*(q-1)
    assert nu in (-1, 1)
    M = q*q-1
    K = q*(q-data['F'])*M+(MC+q*(MF+B-1))*J
    assert 0 < K < q**4
    return dict(q=q, X=X, Y=Y, E=E, A=A, H=H, c=c, k=k, C=C, M=M, K=K,
        gamma=quotient, u=2*d*x+data['inner_bits'], nu=nu,
        eta=eta, zeta=zeta, tau_gap=tau_gap)


def classify_complete(data, period=None):
    """Finite existence criterion for full R<0,mu<0 extensions of fixed data.

    Results contain exact index/rho recipes, not materialized huge witnesses.
    A coarse rejection avoids an unnecessary large first-index period search.
    """
    outer = outer_contract(data)
    A, p = outer['A'], data['p']
    records = []
    coarse_survivors = 0
    for epsilon in (-1, 1):
        lam = epsilon*outer['nu']
        for omega in allowed_signs(p):
            coarse = residues.coarse_classes(A, p, outer['M'], outer['H'], outer['C'],
                outer['K'], outer['gamma'], outer['u'], epsilon, lam, omega)
            if not coarse:
                continue
            coarse_survivors += len(coarse)
            answer = residues.classify(A, p, outer['E'], outer['M'], outer['C'],
                outer['K'], outer['k'], outer['gamma'], outer['u'], epsilon, lam, omega,
                period=period)
            for row in answer['classes']:
                records.append(dict(epsilon=epsilon, lam=lam, omega=omega,
                    period=answer['period'], residue_class=row,
                    auxiliary_recipe=canonical_recipe(A, p, omega)))
    return dict(classes=records, coarse_survivors=coarse_survivors,
        scope='Conditional full-zero existence criterion for fixed validated outer data; '
              'no passing actual outer tuple is asserted by the checker.')


def source_audit():
    source = candidate.sources()[3]
    deps = {name: {name} for name in FIELDS}
    for name in candidate.RETAINED+candidate.eliminated.baseline.prior.CONSTANTS+[
            'x', 'Bm1', 'Kconstant', 'twice_cell_bits']:
        deps.setdefault(name, set())
    for name, op, a, b in source:
        deps[name] = deps.get(a, set()) | deps.get(b, set())
    expected = dict(norm_first=set(), norm_main=set(), norm_input=set(),
        norm_aux={'f', 'i', 'o', 'y_aux'}, norm_index=set(), norm_transport=set(),
        norm_strong={'f', 'i'}, norm_linear={'f', 'j', 'o'})
    assert {n: deps[n] for n in candidate.FACTOR_NAMES} == expected
    rows = aux_rows()
    rng = random.Random(860031)
    cases = 0
    for signed in (False, True):
      for _ in range(96):
        values = {n: rng.randrange(-5, 6) if signed else rng.randrange(1, 7)
                  for n in candidate.RETAINED+['x']}
        fixed = dict(B=16, DC=3, DR=5, MC=10, MF=12, cell_bits=4, inner_bits=3)
        old = candidate.eliminated.run(source, candidate.eliminated.fixed_inputs({**values, **fixed}))
        lifted = {**values, **{n: rng.randrange(-5, 6) if signed else rng.randrange(1, 7) for n in FIELDS}}
        new = candidate.eliminated.run(source, candidate.eliminated.fixed_inputs({**lifted, **fixed}))
        A_math = old['R12']+2
        target = old['index_difference']-1
        local = run_aux(A_math, old['R10a'], target, 1, lifted)
        for n in candidate.FACTOR_NAMES:
            if n in ('norm_strong', 'norm_aux', 'norm_linear'):
                assert new[n] == local[n]
            else:
                assert new[n] == old[n]
        product = 1
        for n in candidate.FACTOR_NAMES:
            product *= local[n] if n in ('norm_strong', 'norm_aux', 'norm_linear') else old[n]
        assert new['polynomial'] == product-1
        cases += 1
    return dict(source=residues.inherited.source_contract(), rebuilt_coordinates=list(FIELDS),
        unchanged_factor_count=5, literal_auxiliary_rows=rows,
        full_source_factor_and_output_identities=cases, signed_cases=cases//2,
        dependency_support={n: sorted(v) for n, v in expected.items()})


def polynomial_audit():
    previous, current = None, [1]
    cases = 0
    for s in range(64):
        ell = 2*s+1
        # Substitute z=1-A^2 into the exact quotient polynomial Q_s(z).
        expanded = [0]*(2*s+1)
        for power, coefficient in enumerate(current):
            for j in range(power+1):
                expanded[2*j] += coefficient*comb(power, j)*(-1)**j
        # Independent closed Chebyshev-binomial formula for psi_A(ell).
        expected = [0]*(2*s+1)
        for j in range(s+1):
            expected[2*s-2*j] = (-1)**(s+j)*comb(2*s-j, j)*2**(2*s-2*j)
        assert expanded == expected
        assert current[0] == (-1)**s*ell
        if s == 0:
            following = [-3, 4]
        else:
            following = [0]*(len(current)+1)
            for j, value in enumerate(current):
                following[j] -= 2*value
                following[j+1] += 4*value
            for j, value in enumerate(previous):
                following[j] -= value
        previous, current = current, following
        cases += 1
    return dict(exact_odd_quotient_polynomial_identities=cases,
                largest_odd_index=127, proof_method='Two-step recurrence, checked against closed binomial coefficients.')


def stepdown_audit():
    cases = matches = parity = 0
    for A in range(3, 9):
      for p in (3, 5, 7):
       for m in range(2*p+2, 2*p+12):
        f = pell(A, m)[0]
        target = pell(A, 2*p)[0]
        assert f > 2*target
        for ell in range(4*m):
            lhs = pell_mod(A, 2*ell, f)[0]
            actual = lhs == target
            expected = ell % (2*m) in (p, 2*m-p)
            assert actual == expected
            matches += actual
            cases += 1
      for p in range(3, 24, 2):
       c = pell(A, p)[1]
       for b in (1, 2, 3, 4):
        m = p*c*b
        s = (-1)**((p-1)//2)
        for j in range(-4, 5):
            sign_f = s*(-1 if j*(m+1) % 2 else 1)
            sign_c = s*(-1 if j*m % 2 else 1)
            if sign_f == -1:
                assert -sign_c in allowed_signs(p)
                assert m % 2 == 0 or p % 4 == 3
            parity += 1
    return dict(exact_modular_stepdown_cases=cases, exact_stepdown_matches=matches,
        auxiliary_parity_and_sign_cases=parity,
        scope='Modular step-down and parity checks; not complete candidate zeros.')


def canonical_audit():
    modular, full = [], []
    hosts = [(A, 3) for A in range(3, 9)]+[(3, 5), (4, 5)]
    for A, p in hosts:
     for omega in allowed_signs(p):
        recipe = canonical_recipe(A, p, omega)
        c, m = recipe['c'], recipe['m']
        f, t = pell(A, m)
        assert t % (c*c) == 0
        T = (A*A-1)*t
        assert f*f-(A*A-1)*t*t == 1
        for j in (0, 1, 3):
            ell = recipe['ell_base']+j*recipe['ell_step']
            residue = pell_mod(T, ell, T*f*c)[0]
            assert residue % T == 0
            V = residue//T
            assert (V+c) % f == 0 and (V+omega*p) % c == 0
            modular.append(dict(A=A, p=p, omega=omega, m=m, ell=ell,
                strong_root_bits=f.bit_length(), scope='Exact modular quotient, not full auxiliary output.'))
        if A <= 5 and p == 3:
            target = omega*p-1000000*c
            _, record = materialize(A, p, target, omega)
            full.append(record)
    return dict(modular_canonical_cases=modular, exact_positive_auxiliary_extensions=full,
        modular_count=len(modular), full_extension_count=len(full),
        scope='The full five-coordinate extensions are auxiliary-only fixtures. No full86 zero is asserted.')


def actual_outer_audit():
    data = dict(B=16, cell_bits=4, inner_bits=3, MC=10, MF=12, DC=3, DR=5,
        Jrep=1, x=1, F=2, alpha=3, w=512, s=2, n=15, p=21)
    X, C = data['w']*16**3, 3
    numerator = (83+X)*C+(16-data['F'])+1
    assert numerator % 15 == 0
    data['zplus'] = numerator//15
    outer = outer_contract(data)
    assert outer['nu'] == -1
    answer = classify_complete(data)
    assert answer['classes'] == [] and answer['coarse_survivors'] == 0
    # Check the literal first, main and transport factors with all other
    # supplied fields positive but deliberately uncompleted.
    values = {n: 1 for n in candidate.RETAINED+['x']}
    values.update({n: data[n] for n in data if n in values})
    values.update(eta=outer['eta'], zeta=outer['zeta'], tau_gap=outer['tau_gap'],
                  rho=1, sigma=outer['gamma']-1)
    fixed = {n: data[n] for n in ('B', 'cell_bits', 'inner_bits', 'MC', 'MF', 'DC', 'DR')}
    env = candidate.eliminated.run(candidate.sources()[3], candidate.eliminated.fixed_inputs({**values, **fixed}))
    assert env['norm_first'] == env['norm_main'] == 1 and env['norm_transport'] == -1
    assert env['polynomial'] != 0
    return dict(data=data, first_main_and_transport_factors=[1, 1, -1],
        canonical_allowed_target_signs=list(allowed_signs(data['p'])),
        complete_negative_input_classes=0, full_candidate_zero=False,
        scope='Actual literal fixed outer arithmetic, rejected by the preceding residue theorem. '
              'DC/DR are not asserted to instantiate a universal program; no passing full outer tuple is supplied.')


def verify():
    return dict(status='PASS_SCOPED_AUXILIARY_SIGN_LIFT', source_audit=source_audit(),
        odd_quotient_identity=polynomial_audit(), stepdown=stepdown_audit(),
        canonical=canonical_audit(), actual_outer=actual_outer_audit(),
        theorem='At fixed A>=3, odd p>=3 and c=psi_A(p), the positive normalized strong/auxiliary/target '
                'system exists exactly for target=-p modc when p=1 mod4, or target=+/-p modc when p=3 mod4.',
        scope='Combined with the prior CRT criterion and validated fixed first/main/transport data, '
              'this is a full negative-input extension criterion. No passing actual outer tuple, '
              'false-input full zero or universal86 theorem is claimed.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    target = Path(__file__).with_suffix('.json')
    if args.write:
        target.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(target.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['theorem'])
    print(result['scope'])
