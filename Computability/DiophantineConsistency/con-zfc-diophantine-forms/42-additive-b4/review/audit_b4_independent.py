#!/usr/bin/env python3
"""Independent B4-code, literal polynomial, and degree audit; stdlib only.

No builder/verifier module is imported. The actual fixed coefficient bytes and
their literal coefficient recipes are evaluated directly. Modular identity
checks are diagnostics; the degree witness and B4 uniqueness are exact finite
certificates for their stated claims.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
from itertools import combinations_with_replacement
import gzip
import json
import sys


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def fixed_residues(directory, prime):
    data = directory / 'data'
    instance = json.loads((data / 'INSTANCE.json').read_text())
    actual = {}
    for name, filename in instance['four_ports'].items():
        actual[name] = int.from_bytes(gzip.decompress((data / filename).read_bytes()), 'little') % prime
    weighted = json.loads((data / 'constants.json').read_text())
    values = {}
    for record in weighted['coefficient_records']:
        val = 0
        for term in record['coefficient_polynomial_in_fixed_ports']:
            v = term['coefficient'] % prime
            for name, power in zip(weighted['fixed_port_order'], term['powers']):
                v = v * pow(actual[name], power, prime) % prime
            val += v
        values[record['name']] = val % prime
    beta_raw = gzip.decompress((data / instance['beta_sun']['file']).read_bytes())
    require(sha256(beta_raw).hexdigest() == instance['beta_sun']['sha256'], 'source-base payload digest')
    values['beta_sun'] = int.from_bytes(beta_raw, 'little') % prime
    return values, weighted['coefficient_records']


def evaluate(circuit, values, fixed, prime):
    out = []
    for n in circuit['nodes']:
        kind = n['kind']
        if kind == 'variable': v = values[n['name']]
        elif kind == 'literal': v = n['value']
        elif kind == 'fixed': v = fixed[n['name']]
        else:
            a, b = out[n['left']], out[n['right']]
            v = a * b if kind == 'mul' else a + b if kind == 'add' else a - b
        out.append(v % prime)
    return out


def literal_formula(v, fixed, records, weights, prime):
    f, g, h, k, l, w, x, y, z, m = [v[n] for n in ('f','g','h','k','l','w','x','y','z','m')]
    mod = lambda a: a % prime
    pp = lambda a, e: pow(a, e, prime)
    t = weights[-1]
    b = mod(1 + 3*f)
    B = mod(fixed['beta_sun'] * pp(b, 4))
    ell = sum(pp(B, wi) for wi in weights[1:]) % prime
    Dcode = 0
    for rec in records:
        alpha = rec['alpha'][1:]
        exponent = 4*t - sum(a*wi for a, wi in zip(alpha, weights[1:]))
        require(exponent >= 0, 'negative source exponent')
        Dcode += fixed[rec['name']] * pp(B, exponent)
    Dcode %= prime
    N0, N1 = pp(B, t+1), mod(4*pp(B, 8*t+1))
    N = mod(N0*N1)
    Ccap = mod(b*pp(B, t))
    Mcode = mod(N0-1-(b-1)*ell)
    Tcode = mod(Mcode+(B-2)*pp(B, 4*t)*N0)
    # The audit may divide in a finite field; the delivered circuit never does.
    geom = (8*t+1) % prime if B == 1 else mod((pp(B, 8*t+1)-1)*pow((B-1) % prime, -1, prime))
    Jcode = mod(2*pp(1+g,4)*Dcode+B*geom)
    Scode = mod(g+Jcode*N0)
    Rcode = mod((Scode+Tcode+1)*N+Tcode+1)
    X, Y = mod((N-1)*Rcode), pp(N,2)
    L = mod(l*Y)
    U, V, W = mod(2*L*X), mod(4*g*w*Y), mod(b*w)
    A = mod(U*(V+1)); Bs = mod(2*X+1); C = mod(Bs+(A-2)*h)
    Pn = mod(U*U*V); K = mod(X+1+k*(Pn-2)); S = mod(2*A-5)
    Ts = mod(3*W*C-2*(W*W-1)); R2 = mod((Pn*Pn-4)*K*K+4)
    Delta = mod(8*pp(Ccap,3)*g*K*K-g*g*(32*pp(C-K*L,2)*pp(Ccap,3)+g*g*K*K))
    O = mod(f*f*l*l*Delta); xi = mod(z*x)
    Ds = mod((A*A-4)*C*C+4); E = mod(C*C*Ds*xi)
    F = mod(4*(A*A-4)*E*E+1)
    G = mod(2*(A+2)*pp(A-2,2)*E*E-1)
    Omega = mod(16*E); H = mod(C+(Bs-C)*F+Omega*F*y)
    Is = mod((G*G-1)*H*H+1)
    r = mod(Ts+S*y); Sigma = mod(xi*pp(S,5))
    Theta = mod((pp(r,3)-r*S*S-pp(S,3))*(r*r+23*S*S))
    r0 = mod(b*(1+(3*O-4)*b*b*z*z)); r1 = R2; r2 = mod(Ds*F*Is)
    w0, w1, w2 = 1, r0, mod(r0*(Pn*Pn+K*K+3))
    center = mod(Sigma*m-Theta)
    A0, A1, A2 = [mod(Sigma*Sigma*ww*ww*rr) for ww, rr in ((w0,r0),(w1,r1),(w2,r2))]
    Vn = mod(center*center+A2-A0-A1)
    Wn = mod(Vn*Vn+4*center*center*A2-4*A0*A1)
    final = mod(Wn*Wn-16*Vn*Vn*center*center*A2)
    return {'b':b, 'base':B, 'ell':ell, 'Dcode':Dcode, 'N0':N0, 'N1':N1,
            'N':N, 'Ccap':Ccap, 'Mcode':Mcode, 'Tcode':Tcode, 'Jcode':Jcode,
            'Scode':Scode, 'Rcode':Rcode, 'X':X, 'Y':Y, 'Lsmall':L,
            'U':U, 'V':V, 'Wsmall':W, 'A':A, 'Bsmall':Bs, 'C':C, 'Pn':Pn,
            'K':K, 'Ssmall':S, 'Tsmall':Ts, 'R2':R2, 'Delta':Delta, 'O0':O,
            'xi':xi, 'D':Ds, 'E':E, 'F':F, 'Gstar':G, 'Omega':Omega,
            'Hstar':H, 'Istar':Is, 'Sigma':Sigma, 'Theta':Theta,
            'A1':r0, 'A2':r1, 'A3':r2, 'norm_weight1':w1, 'norm_weight2':w2,
            'norm_center':center, 'scaled_A1':A0, 'scaled_A2':A1, 'scaled_A3':A2,
            'F10':final}


def audit(directory):
    circuit_path = directory / 'generated' / 'b4_signed10.json'
    circuit_raw = circuit_path.read_bytes()
    circuit = json.loads(circuit_raw)
    vars_expected = ['f','g','h','k','l','w','x','y','z','m']
    require(circuit['variables'] == vars_expected, 'witness list')
    require([n['name'] for n in circuit['nodes'] if n['kind']=='variable'] == vars_expected, 'hidden witness')
    require(all(n['kind'] in {'variable','literal','fixed','add','sub','mul'} for n in circuit['nodes']), 'nonpolynomial gate')
    counts = Counter(n['kind'] for n in circuit['nodes'])
    require(sum(counts[k] for k in ('add','sub','mul')) == 2204, 'operation ledger')
    live = {circuit['output']}
    for i in range(len(circuit['nodes'])-1,-1,-1):
        n = circuit['nodes'][i]
        if n['kind'] in ('add','sub','mul'):
            require(0 <= n['left'] < i and 0 <= n['right'] < i, 'non-topological DAG')
            if i in live: live.update((n['left'], n['right']))
    require(len(live) == len(circuit['nodes']), 'dead node')
    code = json.loads((directory / 'bose_chowla32.json').read_text())
    weights = code['weights']
    require(len(weights)==32 and weights[0]==0 and weights[-1]==942302 and weights==sorted(set(weights)), 'weight ordering')
    sums = [sum(weights[i] for i in tup) for tup in combinations_with_replacement(range(32),4)]
    require(len(sums)==52360 and len(set(sums))==52360, 'integer B4 collision')
    require(len({s % 1048575 for s in sums})==52360, 'modular B4 collision')
    degree = []
    for n in circuit['nodes']:
        k=n['kind']
        if k=='variable': d=1
        elif k in ('literal','fixed'): d=0
        elif k=='mul': d=degree[n['left']]+degree[n['right']]
        else: d=max(degree[n['left']],degree[n['right']])
        degree.append(d)
    D=degree[circuit['output']]
    require(D==107286763576, 'degree upper bound')
    degree_witnesses=[]
    literal_checks=0
    for prime in (101,1009,1000003):
        fixed, records = fixed_residues(directory,prime)
        leading=[]
        for i,n in enumerate(circuit['nodes']):
            k=n['kind']
            if k=='variable': v=1
            elif k=='literal': v=n['value']
            elif k=='fixed': v=fixed[n['name']]
            elif k=='mul': v=leading[n['left']]*leading[n['right']]
            else:
                a=leading[n['left']] if degree[n['left']]==degree[i] else 0
                b=leading[n['right']] if degree[n['right']]==degree[i] else 0
                v=a+b if k=='add' else a-b
            leading.append(v % prime)
        require(leading[circuit['output']] != 0, 'degree attainment failed')
        degree_witnesses.append({'prime':prime,'degree':D,'coefficient':leading[circuit['output']]})
        # Signed and degenerate values deliberately include f=0 and base=0.
        assignments=[dict(zip(vars_expected, row)) for row in
                     [range(10),range(-10,0),[1]*10,[0]*10,[2,-3,5,-7,11,-13,17,-19,23,-29]]]
        assignments.append(dict(zip(vars_expected, [(-pow(3,-1,prime))%prime,2,3,4,5,6,7,8,9,10])))
        for assignment in assignments:
            actual=evaluate(circuit,assignment,fixed,prime)
            expected=literal_formula(assignment,fixed,records,weights,prime)
            for name,value in expected.items():
                require(actual[circuit['named_nodes'][name]]==value, 'literal formula mismatch: '+name)
                literal_checks+=1
    return {'status':'PASS','circuit_sha256':sha256(circuit_raw).hexdigest(),
            'variables':vars_expected,'operations':2204,'operation_counts':{k:counts[k] for k in ('add','sub','mul')},
            'all_nodes_live':True,'only_polynomial_gates':True,'fixed_coefficients_read_from_actual_payloads':True,
            'b4_multisets':52360,'integer_sums_distinct':True,'sums_distinct_modulo_1048575':True,
            'degree_upper_bound':D,'degree_attainment':degree_witnesses,
            'named_literal_formula_checks':literal_checks,
            'scope':'Exact B4/degree certificates and independent modular transcription diagnostics; no proof of the imported Lucas or compiler theorems.'}


if __name__=='__main__':
    directory=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'ten_integer'
    result=audit(directory)
    output=Path(sys.argv[2]) if len(sys.argv)>2 else Path(__file__).with_name('B4_INDEPENDENT_AUDIT.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
