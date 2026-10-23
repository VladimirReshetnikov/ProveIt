#!/usr/bin/env python3
"""Deterministic finite audit of the 76-operation, degree-44 circuit.

Uses Python's standard library only.  All checks remain active under -O.
This is not a replacement for the inherited compiler/Pell proof.
"""
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

HERE = Path(__file__).resolve().parent


def require(condition, description):
    if not condition:
        raise ValueError(description)


def add(a, b, sign=1):
    result = dict(a)
    for monomial, coefficient in b.items():
        result[monomial] = result.get(monomial, 0) + sign * coefficient
        if result[monomial] == 0:
            del result[monomial]
    return result


def mul(a, b):
    result = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            m = tuple(x + y for x, y in zip(ma, mb))
            result[m] = result.get(m, 0) + ca * cb
    return {m: c for m, c in result.items() if c}


def power(a, n):
    size = len(next(iter(a)))
    result = {(0,) * size: 1}
    for _ in range(n):
        result = mul(result, a)
    return result


def check_identities():
    # Exact polynomial-ring identities, not random-point evidence.
    z = (0, 0, 0)
    one = {z: 1}
    def var(n):
        e = [0, 0, 0]
        e[n] = 1
        return {tuple(e): 1}
    L, r, k = [var(j) for j in range(3)]
    lhs = add(power(add(L, r), 2), mul(L, add(L, k)), -1)
    rhs = add(power(r, 2), mul(L, add(add(r, r), k, -1)))
    require(lhs == rhs, 'first root-offset identity')
    A, V, u = [var(j) for j in range(3)]
    Y = add(V, u)
    lhs = add(mul(A, add(power(V, 2), power(Y, 2), -1)), power(Y, 2))
    rhs = add(power(Y, 2), mul(mul(A, u), add(V, Y)), -1)
    require(lhs == rhs, 'auxiliary root-offset identity')
    # The main Pell norm loses its apparent degree-22 terms exactly.
    def variable4(n):
        e = [0, 0, 0, 0]
        e[n] = 1
        return {tuple(e): 1}
    a, c, H, Z = [variable4(j) for j in range(4)]
    lhs = add(power(add(mul(a, c), Z), 2), mul(add(power(a, 2), H), power(c, 2)), -1)
    rhs = add(add(power(Z, 2), mul(add(mul(a, c), mul(a, c)), Z)), mul(H, power(c, 2)), -1)
    require(lhs == rhs, 'main Pell cancellation identity')
    return 3


def check_pell_examples():
    count = 0
    for n in range(2, 15):
        # Positive norm-one units for x^2-n(n+1)k^2=1.
        x, k = 1, 0
        for _ in range(1, 7):
            x, k = (2*n+1)*x + 2*n*(n+1)*k, 2*x + (2*n+1)*k
            L = n*k
            r = x-L
            require(r > 0 and r*r + L*(2*r-k) == 1, 'positive first offset')
            count += 1
    for M in range(2, 30):
        V, Y = 4*M*M-3, 4*M*M-1
        u = Y-V
        require(V > 1 and u > 0, 'auxiliary positive offset')
        require((V+u)**2-M*M*u*(2*V+u) == 1, 'auxiliary norm example')
        count += 1
    return count


def check_complete_formula(circuit):
    rng = random.Random(20261023)
    for trial in range(80):
        values = {n: rng.randint(-3, 4) for n in circuit['witnesses']}
        values.update(beta=15, K0=43, MC=18, MF=79)
        J,F,alpha,z,f,h,i,T,s,w,r,eta,zeta,u,gamma = [values[n] for n in circuit['witnesses']]
        q = values['beta']*J+1
        C = q-F-alpha
        X,Y = w*q,s*q**3
        E,k = X*Y,eta+zeta
        c,a = k*Y+eta,E+Y
        H = 4*a+3
        Delta = a*a+H
        D,L = X+a*c+gamma*H,E*k*Y
        G = (q-1)*(q-F)+alpha
        R = G*(q*q-1)+(values['MC']+q*values['MF'])*J
        V = c*(T*f-1)-R*f*f
        A0,I = Delta*(f*f-1),i*c*c
        N0 = r*r+L*(2*r-k)
        N1 = D*D-Delta*c*c
        Na = (V+u)**2-A0*u*(2*V+u)
        Nk = k-h*E-R
        Nt = (values['K0']+w)*C+(q-F)-z*(q-1)
        expected = (N0*Nk-1)**2+(N1*Nt-1)**2+(Na-1)**2+(I*I-A0)**2
        def read(v):
            return v if type(v) is int else values[v]
        for name,op,a,b in circuit['source']:
            aa,bb = read(a),read(b)
            values[name] = aa+bb if op == '+' else aa-bb if op == '-' else aa*bb
        require(values[circuit['output']] == expected, 'full formula diagnostic '+str(trial))
    return 80


def audit():
    path = HERE / 'offset44.json'
    circuit = json.loads(path.read_text())
    witnesses = circuit['witnesses']
    ports = circuit['fixed_numerals']
    names = witnesses + ports
    require(len(witnesses) == 15 and len(ports) == 4, 'coordinate counts')
    require(len(set(names)) == len(names), 'duplicate coordinate')
    require(witnesses == ['J','F','alpha','z','f','h','i','T','s','w','r','eta','zeta','u','gamma'], 'coordinate order')
    require(ports == ['beta','K0','MC','MF'], 'fixed port convention')
    upstream_path = HERE / 'upstream/p69_unscaled.json'
    require(hashlib.sha256(upstream_path.read_bytes()).hexdigest() == circuit['source_sha256'], 'source snapshot hash')
    require(circuit['coefficient_binding']['source_package'] == '31-sun10', 'whole coefficient binding')
    binding_path = HERE / 'upstream/package31_COEFFICIENT_BINDING.json'
    binding = json.loads(binding_path.read_text())
    require(binding['B'] == '2^1064921' and binding['instance'] == 'wang943-mixed-121x8801', 'wrong coefficient tuple')
    zero = (0,) * len(names)
    def scalar(n):
        return {zero: n} if n else {}
    def variable(n):
        e = list(zero)
        e[names.index(n)] = 1
        return {tuple(e): 1}
    state = {n: (1 if n in witnesses else 0, variable(n)) for n in names}
    producers = {}
    count = Counter()
    def read(v):
        if type(v) is int:
            return 0, scalar(v)
        require(type(v) is str and v in state, 'undefined operand '+str(v))
        return state[v]
    identities = check_identities()
    main_matrix = {
        'cam2': ['cam2','*','R10a','R12'],
        'D1': ['D1','+','wn2','cam2'],
        'gam': ['gam','*','gamma','a4m5'],
        'R14': ['R14','+','D1','gam'],
        'L15': ['L15','*','R14','R14'],
        'a_square': ['a_square','*','R12','R12'],
        'A': ['A','+','a_square','a4m5'],
        'c2': ['c2','*','R10a','R10a'],
        'Ac2': ['Ac2','*','A','c2'],
        'norm_main': ['norm_main','-','L15','Ac2'],
    }
    for row in circuit['source']:
        require(type(row) is list and len(row) == 4, 'invalid gate')
        name, op, a, b = row
        if name in main_matrix:
            require(row == main_matrix[name], 'main norm structure changed')
        require(name not in state and op in ('+', '-', '*'), 'invalid producer')
        da, pa = read(a)
        db, pb = read(b)
        if op == '*':
            degree, leading = da+db, mul(pa, pb)
        else:
            degree = max(da, db)
            leading = add(pa if da == degree else {}, pb if db == degree else {}, 1 if op == '+' else -1)
        if name == 'norm_main':
            # With Z=X+gamma H, the checked identity is
            # N1=Z^2+2*a*c*Z-H*c^2.  Its term degrees are14,18,16.
            require(state['wn2'][0] == 2 and state['gam'][0] == 7 and
                    state['cam2'][0] == 11 and state['a4m5'][0] == 6 and
                    state['c2'][0] == 10, 'main norm degree premises')
            degree = 18
            leading = mul(scalar(2), mul(state['cam2'][1], state['gam'][1]))
        # Cancellation leaves a valid upper envelope, which is enough for
        # the degree-44 claim. No false exact degree is inferred at that gate.
        require(all(sum(e[:15]) == degree for e in leading), 'weight mismatch')
        state[name] = degree, leading
        producers[name] = (a, b)
        count[op] += 1
    live, pending = set(), [circuit['output']]
    while pending:
        name = pending.pop()
        if type(name) is not str or name in live:
            continue
        live.add(name)
        pending.extend(producers.get(name, ()))
    require(live == set(state), 'dead gates/coordinates: '+str(set(state)-live))
    require(sum(count.values()) == 76, 'gate count')
    require(state['polynomial'][0] == 44, 'total-degree envelope')

    Q = mul(variable('beta'), variable('J'))
    k = add(variable('eta'), variable('zeta'))
    lead_strong = mul(power(variable('i'), 4), power(k, 8))
    lead_strong = mul(lead_strong, mul(power(variable('s'), 8), power(Q, 24)))
    lead_aux = mul(scalar(4), power(k, 2))
    for n, d in [('w', 4), ('s', 6), ('T', 2), ('f', 6), ('u', 2)]:
        lead_aux = mul(lead_aux, power(variable(n), d))
    lead_aux = mul(lead_aux, power(Q, 22))
    expected = add(lead_strong, lead_aux)
    require(state['polynomial'][1] == expected, 'leading homogeneous form')
    distinguished = dict(i=4, eta=8, s=8, J=24, beta=24)
    require(expected.get(tuple(distinguished.get(n, 0) for n in names)) == 1, 'distinguished coefficient beta^24')
    examples = check_pell_examples()
    formula_examples = check_complete_formula(circuit)
    ledger = dict(
        circuit_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        witnesses=15, witness_domain='strictly positive integers', fixed_ports=4,
        operations=76, multiplications=count['*'], additions=count['+'], subtractions=count['-'],
        all_gates_live=True, all_ports_live=True, exact_degree=44,
        residual_degree_upper_bounds={n: state[n][0] for n in ['residual_main_transport','residual_aux','residual_strong','residual_first_index']},
        leading_homogeneous_form='i^4*(eta+zeta)^8*s^8*(beta*J)^24 + 4*(eta+zeta)^2*w^4*s^6*T^2*f^6*u^2*(beta*J)^22',
        distinguished_monomial='i^4*eta^8*s^8*J^24', distinguished_coefficient='beta^24',
        exact_degree_hypothesis='beta != 0', exact_polynomial_identity_checks=identities,
        elementary_pell_diagnostic_examples=examples,
        complete_formula_diagnostic_examples=formula_examples,
        whole_coefficient_binding='31-sun10: wang943-mixed-121x8801, B=2^1064921',
        coefficient_binding_sha256=hashlib.sha256(binding_path.read_bytes()).hexdigest(),
        proof_boundary='Finite gate/degree/identity certificate. Semantic equivalence uses the supplied ordinary mathematical proof and inherited compiler/strong-rank interfaces; no new formal proof is claimed.'
    )
    (HERE / 'offset44.audit.json').write_text(json.dumps(ledger, indent=2)+'\n')
    print(json.dumps(ledger, indent=2))


if __name__ == '__main__':
    audit()
