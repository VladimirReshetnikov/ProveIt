#!/usr/bin/env python3
"""Independent exact audit of the final eleven-positive circuit.

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
        'Fa': 'F+alpha', 'M': 'q3*qm',
        'Bt': '(q*K0+X)*C-q*F', 'ellk': 'ell+k',
        'Dtau': 'ell*ellk+1', 'I2': 'I*I', 'fm': 'Delta*I2',
        'Df': 'fm+1', 'Q': 'Delta*fm', 'delta': 'Q-1',
        'Told': 'T+Fa', 'cT': 'c*Told', 'V': 'Df*(cT-R)-c',
        'fmajor':'(a+2)*I', 'L': 'k*Told',
        'W': '1+qm*L',
        'Zbar': 'M*(ellk+n+L+V+fmajor)+qm*Y-q3*W*Bt',
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
    require(sum(counts.values()) == packet['operations'] == 112, 'gate count')
    require(dict(counts) == packet['operation_breakdown'] ==
            {'*':64,'+':31,'-':17}, 'gate breakdown')
    require(system_count == packet['system_operations'] == 109, 'system cost')
    return {'exact_named_contracts': len(seen), 'all_gates_and_inputs_live': True,
            'operations': 112, 'operation_breakdown': dict(counts),
            'system_operations': system_count}


def check_universal_identities():
    sy = {x:Ring.variable(x) for x in
          ['x','r','s','t','a','b','c','d','z','A','B','C','U','H','X','v','Q','M','V']}
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
    QQ,MM,VV,zz,AA,BB = [sy[n] for n in ['Q','M','V','z','A','B']]
    centered_original=(QQ-1)*((zz+MM*VV)**2-AA-BB)-MM**2*(QQ*VV**2-1)
    centered_resolved=(QQ-1)*(zz*(zz+2*MM*VV)-AA-BB)-MM**2*(VV**2-1)
    require(centered_original==centered_resolved, 'centered norm degree cancellation')
    # Resolve the main Pell degree cancellation in the actual DAG.
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
        if name == 'Jn':
            require(value == 0 and bound == 62, 'apparent centered terms did not cancel')
            require([degree[x] for x in ['Q','M','V','fmajor','L','Bt']] == [18,4,18,7,2,2],
                    'centered cancellation degree premises')
            value=2*env['Q']*env['M']**2*env['V']*env['fmajor']
            bound=51
        if name == 'Ncenter':
            require(value == 0 and bound == 102, 'double-center cancellation missing')
            zsmall0=p**4*(env['ell']-env['L']*env['Bt'])
            value=8*env['Q']**2*(env['M']*env['fmajor'])*(env['M']*env['V'])**2*zsmall0
            bound=99
        require(value != 0, 'unexpected leading cancellation at '+name)
        env[name],degree[name] = value,bound
    expected_degrees = {'I':5,'Df':14,'Q':18,'V':18,'fmajor':7,'L':2,'W':3,
                        'Zbar':22,'A':16,'Bf':22,'Cnum':62,'Jn':51,'Ncenter':99,
                        'N8':198,'A1':13,'P11':211}
    require({x:degree[x] for x in expected_degrees} == expected_degrees,
            'exact degree contract mismatch')
    I0 = sy['i']*k*k*sy['Y']**2
    Df0 = sy['X']**2*sy['Y']**2*I0**2
    Q0 = sy['X']**4*sy['Y']**4*I0**2
    Bt0 = (sy['K0']*p+sy['X'])*(p-sy['F']-sy['alpha'])-p*sy['F']
    R0 = p**3*(p-sy['F'])
    fmajor0 = sy['X']*sy['Y']*I0
    L0 = k*(sy['T']+sy['F']+sy['alpha'])
    ell0 = sy['X']*k*sy['Y']**2
    z0 = p**4*(ell0-L0*Bt0)
    V0 = -Df0*R0
    main0 = 32*p**2*k*sy['X']**2*sy['Y']**4*\
            (4*p**2*sy['Y']*sy['gamma']+R0)
    require(env['Df'] == Df0 and env['Q'] == Q0, 'strong leading forms')
    require(env['L'] == L0 and env['Zbar'] == p**4*V0, 'transport leading forms')
    require(env['A1'] == main0, 'main leading form')
    require(env['Jn'] == 2*Q0*p**8*V0*fmajor0, 'centered leading form')
    require(env['Ncenter'] == 8*Q0**2*(p**4*fmajor0)*(p**4*V0)**2*z0,
            'doubly centered norm-center leader')
    require(env['N8'] == 64*Q0**4*p**32*Df0**4*R0**4*fmajor0**2*L0*Bt0*(L0*Bt0-2*ell0),
            'norm leading form')
    require(env['P11'] == env['N8']*main0, 'final product leading form')
    unknowns = set(packet['witnesses'])|{'q0','k0'}
    require(env['P11'].degree(unknowns) == 211, 'leader not degree211')
    monomial = {'q0':48,'i':18,'k0':39,'X':30,'Y':67,'T':2,'F':4,'alpha':2,'gamma':1}
    selected = env['P11'].coefficient(monomial,unknowns)
    require(selected == 2**13, 'degree211 selected coefficient')
    require(packet['exact_degree'] == 211 and packet['residual_degrees'] == [198,13],
            'declared degree mismatch')
    return {'exact_degrees':expected_degrees,
            'leading_form_monomials_in_q0_k0_coordinates':len(env['P11'].terms),
            'leading_coordinate_definitions':{'q0':'3*beta*j','k0':'eta+zeta'},
            'selected_original_monomial':
              'j^48*i^18*eta^39*X^30*Y^67*T^2*F^4*alpha^2*gamma',
            'selected_fixed_slice_coefficient':'2^13*(3*beta)^48',
            'generic_gate_degree_without_cancellation_is_not_used':True}


def check_double_center():
    names=['z','aa','bb','cc','ee','ff']
    z,a,b,c,e,f=[Ring.variable(x) for x in names]
    x=z+b+c; B=b*b-e; C=c*c-f
    center=(x*x-a-B-C)**2-4*(a*B+a*C+B*C)
    norm=center**2-64*a*B*C*x*x
    weights=dict(zip(names,[8,16,11,22,18,26]))
    def leading(poly):
        d=max(sum(weights[n]*v for n,v in mon) for mon in poly.terms)
        return d,Ring({mon:coef for mon,coef in poly.terms.items()
                       if sum(weights[n]*v for n,v in mon)==d})
    dc,lc=leading(center); dn,ln=leading(norm)
    require(dc+36==99 and lc==8*b*c*c*z, 'double-center upper bound')
    require(dn+72==198 and ln==64*b*b*c**4*(z*z-a), 'double-norm upper bound')
    require(max(dict(mon).get('ff',0) for mon in norm.terms)<=4,
            'denominator clears with delta fourth power')
    cert={'variables':names,'weights':weights,'center_terms':len(center.terms),
          'norm_terms':len(norm.terms),'cleared_center_degree':99,
          'cleared_norm_degree':198,'substitutions':{
              'z':'Zbar-M*V-M*(a+2)*I','aa':'A','bb':'M*(a+2)*I',
              'cc':'M*V','ee':'M^2*(I^2-1)','ff':'-M^2*(V^2-1)/delta'},
          'norm_coefficients':[{'monomial':dict(mon),'coefficient':coef}
                               for mon,coef in sorted(norm.terms.items())]}
    (ROOT/'DOUBLE_CENTER_CERTIFICATE.json').write_text(json.dumps(cert,indent=2)+'\n')
    return {'center_terms':len(center.terms),'norm_terms':len(norm.terms),
            'cleared_center_degree':99,'cleared_norm_degree':198,
            'center_leader':'8*bb*cc^2*z','norm_leader':'64*bb^2*cc^4*(z^2-aa)'}


def main():
    path = ROOT/'p11_positive_degree211.json'
    raw = path.read_bytes()
    packet = json.loads(raw)
    result = {'status':'PASS','checker':'separate exact cut-contract sparse-ring audit of the new circuit',
              'source_pin':'2605669a532342f153b13eb6b4a0af4b54f5fa37',
              'packet_sha256':hashlib.sha256(raw).hexdigest(),
              'literal':check_literal(packet),
              'universal_identities':check_universal_identities(),
              'double_center_identity':check_double_center(),
              'exact_degree':check_leading_forms(packet),
              'scope':'Finite literal algebra, leading forms, liveness and costs; '
                      'see PROOF.md for the new universal reduction and its inherited semantic boundary.'}
    (ROOT/'ALGEBRA_AUDIT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))


if __name__ == '__main__':
    main()
