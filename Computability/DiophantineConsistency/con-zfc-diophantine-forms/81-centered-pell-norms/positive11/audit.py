#!/usr/bin/env python3
"""Exact cut and leading-form audit of the modified eleven-positive circuit.

Adapted from source70 independent_audit.py. This is not claimed as an
independently authored new audit; separate mathematical review is supplied.

The construction builder and its verifier are not imported.  Polynomial
arithmetic comes from the separately authored standard-library sparse ring.
This audit checks finite algebra, not the unbounded existence theorem.
"""
from pathlib import Path
from collections import Counter
from itertools import product
import hashlib
import json
from independent_ring import Ring, expand, require

ROOT = Path(__file__).resolve().parent


def check_literal(packet):
    formulas = {
        'J': '3*j+1', 'qm': 'J*beta', 'q': 'qm+1', 'q2': 'q*q',
        'q3': 'q*q2', 'q2m': 'q2-1', 'qF': 'q-F', 'C': 'qF-alpha',
        'E': 'X*Y', 'k': 'eta+zeta', 'kY': 'k*Y', 'c': 'kY+eta',
        'c2': 'c*c', 'I': 'i*c2', 'a': 'E+Y', 'H': '4*a+3',
        'Delta': 'a*a+H', 'ac': 'a*c', 'b0': 'X+ac', 'ell': 'E*kY',
        'G': 'qm*qF+alpha', 'R': 'G*q2m+(MC+q*MF)*J',
        'Rhat': 'q3*(q+F+alpha)', 'M': 'q3*qm',
        'Bt': '(q*K0+X)*C-q*F', 'ellk': 'ell+k',
        'Dtau': 'ell*ellk+1', 'I2': 'I*I', 'fm': 'Delta*I2',
        'Df': 'fm+1', 'Q': 'Delta*fm', 'delta': 'Q-1', 'cT': 'c*T',
        'V': 'Df*(cT-R)-c', 'Vbar': 'Df*(cT+Rhat)', 'L': '3*Vbar',
        'W': '1+qm*L',
        'Zbar': 'M*(ellk+n+L)+qm*Y-q3*W*Bt',
        'r0': 'k-R-1', 'S': '4*q*Y', 'U': 'q*S',
        'shift': 'U*gamma+S*X-r0', 'Dstar': 'U*b0+H*shift',
        'A1': 'Dstar*Dstar-U*U*(1+Delta*c2)', 'M2': 'M*M',
        'A': 'M2*Dtau', 'Bf': 'M2*Df', 'Dnum': 'Q*V*V-1',
        'Cnum': 'M2*Dnum', 'z2': 'Zbar*Zbar', 'ABsum': 'A+Bf',
        'AB': 'A*Bf', 'delta2': 'delta*delta', 'Tn': 'delta2*AB',
        'Rn': 'delta*Cnum', 'Jn': 'delta*(z2-ABsum)-Cnum',
        'Ncenter': 'Jn*Jn-4*(Tn+Rn*ABsum)',
        'normtail': '64*Tn*Rn*z2', 'N8': 'Ncenter*Ncenter-normtail',
    }
    witnesses = ['j','F','alpha','i','T','X','Y','n','eta','zeta','gamma']
    ports = ['beta','K0','MC','MF']
    require(packet['witnesses'] == witnesses, 'wrong ordered witness list')
    require(packet['fixed_numerals'] == ports, 'wrong fixed coefficient ports')
    names = witnesses + ports + [row[0] for row in packet['source']]
    require(len(names) == len(set(names)), 'duplicate input or gate name')
    sy = {name: Ring.variable(name) for name in names}
    env = {name: sy[name] for name in witnesses+ports}
    seen, deps, counts = set(), {}, Counter()
    for name, op, left, right in packet['source']:
        a = Ring.numeral(left) if type(left) is int else env[left]
        b = Ring.numeral(right) if type(right) is int else env[right]
        require(op in ('+','-','*'), 'invalid binary operation')
        value = a+b if op == '+' else a-b if op == '-' else a*b
        deps[name] = {x for x in (left,right) if type(x) is str}
        counts[op] += 1
        if name in formulas:
            require(value == expand(formulas[name],sy), 'cut mismatch: '+name)
            seen.add(name)
            env[name] = sy[name]
        else:
            env[name] = value
    require(seen == set(formulas), 'missing or unchecked named cut')
    require(env[packet['output']] == sy['N8']+sy['A1']+sy['N8']*sy['A1'],
            'wrong finalizer')
    def reachable(roots):
        live = set()
        def visit(name):
            if name in live:
                return
            live.add(name)
            for child in deps.get(name,()):
                visit(child)
        for root in roots:
            visit(root)
        return live
    require(reachable([packet['output']]) == set(names), 'dead gate or input')
    gate_names = set(deps)
    system_count = len(reachable(['N8','A1']) & gate_names)
    require(sum(counts.values()) == packet['operations'] == 111, 'gate count')
    require(dict(counts) == packet['operation_breakdown'] ==
            {'*':65,'+':29,'-':17}, 'gate breakdown')
    require(system_count == packet['system_operations'] == 108, 'system cost')
    return {'exact_named_contracts': len(seen), 'all_gates_and_inputs_live': True,
            'operations': 111, 'operation_breakdown': dict(counts),
            'system_operations': system_count}


def check_universal_identities():
    sy = {x:Ring.variable(x) for x in
          ['x','r','s','t','a','b','c','d','z','A','B','C','U','H','X','v']}
    x,r,s,t = [sy[name] for name in ['x','r','s','t']]
    conjugates = Ring.numeral(1)
    for er,es,et in product((-1,1),repeat=3):
        conjugates = conjugates * (x-er*r-es*s-et*t)
    a,b,c = r*r,s*s,t*t
    norm = ((x*x-a-b-c)**2-4*(a*b+a*c+b*c))**2-64*a*b*c*x*x
    require(conjugates == norm, 'eight-conjugate norm identity')
    # Check the rational radical-extraction formulas without division.
    total = r+s+t
    u = r*s+r*t+s*t
    v = r*s*t
    require(total*total-a-b-c == 2*u, 'first root-extraction identity')
    require(u*u-a*b-a*c-b*c == 2*total*v, 'product extraction identity')
    require(a*total+v == r*(r+s)*(r+t), 'extraction denominator factorization')
    require(r*(a*total+v) == a*(a+u), 'rational root-extraction numerator')
    d,z,A,B,C = [sy[name] for name in ['d','z','A','B','C']]
    compressed = (d*(z*z-A-B)-C)**2-4*(d*d*A*B+d*C*(A+B))
    original = d*d*((z*z-A-B)**2-4*A*B)-2*d*C*(z*z+A+B)+C*C
    symmetric = (d*z*z-d*A-d*B-C)**2-4*(d*d*A*B+d*C*(A+B))
    require(compressed == original == symmetric, 'norm-center compression')
    require(64*(d*d*A*B)*(d*C)*z*z == 64*d**3*A*B*C*z*z,
            'norm-tail compression')
    # Resolve the only degree cancellation in the actual DAG.
    U,H,X,aa,cc,shift = [sy[name] for name in ['U','H','X','a','c','v']]
    small = U*X+H*shift
    full = (U*(X+aa*cc)+H*shift)**2-U*U*(1+(aa*aa+H)*cc*cc)
    reduced = 2*U*aa*cc*small+small*small-U*U*H*cc*cc-U*U
    require(full == reduced, 'main Pell degree cancellation')
    require((1+sy['a'])*(1+sy['b'])-1 == sy['a']+sy['b']+sy['a']*sy['b'],
            'product finalizer identity')
    return {'eight_conjugate_identity': True, 'elementary_root_extraction': True,
            'norm_center_and_tail_compression': True,
            'main_degree_cancellation': True, 'unit_product_identity': True}


def check_leading_forms(packet):
    names = packet['witnesses']+packet['fixed_numerals']
    sy = {x:Ring.variable(x) for x in names+['q0','k0']}
    env = {x:sy[x] for x in names}
    degree = {x:1 if x in packet['witnesses'] else 0 for x in names}
    p,k = sy['q0'],sy['k0']
    def operand(x):
        return (Ring.numeral(x),0) if type(x) is int else (env[x],degree[x])
    for name,op,left,right in packet['source']:
        a,da = operand(left); b,db = operand(right)
        if op == '*':
            value, bound = a*b, da+db
        elif da > db:
            value, bound = a,da
        elif db > da:
            value, bound = (b if op == '+' else -b),db
        else:
            value, bound = (a+b if op == '+' else a-b),da
        if name == 'qm':
            require(value == 3*sy['beta']*sy['j'], 'radix leading substitution')
            value = p
        if name == 'k':
            require(value == sy['eta']+sy['zeta'], 'k leading substitution')
            value = k
        if name == 'A1':
            require(value == 0 and bound == 14, 'apparent main terms did not cancel')
            require([degree[x] for x in ['U','a','c','H','shift']] == [3,2,2,2,4],
                    'main cancellation degree premises')
            # The checked universal identity leaves this unique degree-13 term;
            # all its other summands have degree at most 12.
            value = 2*env['U']*env['a']*env['c']*env['H']*env['shift']
            bound = 13
        require(value != 0, 'unexpected leading cancellation at '+name)
        env[name],degree[name] = value,bound
    expected_degrees = {'I':5,'Df':14,'Q':18,'V':18,'Rhat':4,'L':18,'W':19,
                        'Zbar':24,'A':16,'Bf':22,'Cnum':62,'Ncenter':132,
                        'N8':264,'A1':13,'P11':277}
    require({x:degree[x] for x in expected_degrees} == expected_degrees,
            'exact degree contract mismatch')
    I0 = sy['i']*k*k*sy['Y']**2
    Df0 = sy['X']**2*sy['Y']**2*I0**2
    Q0 = sy['X']**4*sy['Y']**4*I0**2
    Bt0 = (sy['K0']*p+sy['X'])*(p-sy['F']-sy['alpha'])-p*sy['F']
    L0 = 3*Df0*p**3*(p+sy['F']+sy['alpha'])
    Z0 = -p**4*L0*Bt0
    main0 = 32*p**2*k*sy['X']**2*sy['Y']**4*\
            (4*p**2*sy['Y']*sy['gamma']+p**3*(p-sy['F']))
    require(env['Df'] == Df0 and env['Q'] == Q0, 'strong leading forms')
    require(env['L'] == L0 and env['Zbar'] == Z0, 'transport leading forms')
    require(env['A1'] == main0, 'main leading form')
    require(env['Ncenter'] == Q0**2*Z0**4, 'norm center leading form')
    require(env['N8'] == env['Ncenter']*env['Ncenter'], 'norm leading form')
    require(env['P11'] == env['N8']*main0, 'final product leading form')
    require(env['P11'].variables() <=
            {'q0','k0','i','X','Y','F','alpha','gamma','K0'},
            'unexpected uncompressed variable in final leading form')
    unknowns = set(packet['witnesses'])|{'q0','k0'}
    require(env['P11'].degree(unknowns) == 277, 'leader not degree277')
    monomial = {'q0':60,'i':24,'k0':49,'X':42,'Y':85,'alpha':16,'gamma':1}
    selected = env['P11'].coefficient(monomial,unknowns)
    require(selected == 2**7*3**8, 'degree277 selected coefficient')
    require(packet['exact_degree'] == 277 and packet['residual_degrees'] == [264,13],
            'declared degree mismatch')
    return {'exact_degrees':expected_degrees,
            'leading_form_monomials_in_q0_k0_coordinates':len(env['P11'].terms),
            'leading_coordinate_definitions':{'q0':'3*beta*j','k0':'eta+zeta'},
            'selected_original_monomial':
              'j^60*i^24*eta^49*X^42*Y^85*alpha^16*gamma',
            'selected_fixed_slice_coefficient':'2^7*3^8*(3*beta)^60',
            'generic_gate_degree_without_cancellation_is_not_used':True}


def main():
    path = ROOT/'p11_positive_degree277.json'
    raw = path.read_bytes()
    packet = json.loads(raw)
    result = {'status':'PASS','checker':'independent standard-library sparse ring',
              'source_pin':'2605669a532342f153b13eb6b4a0af4b54f5fa37',
              'packet_sha256':hashlib.sha256(raw).hexdigest(),
              'literal':check_literal(packet),
              'universal_identities':check_universal_identities(),
              'exact_degree':check_leading_forms(packet),
              'scope':'Finite literal algebra, leading forms, liveness and costs; '
                      'see independent mathematical review for the unbounded proof.'}
    (ROOT/'INDEPENDENT_AUDIT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
