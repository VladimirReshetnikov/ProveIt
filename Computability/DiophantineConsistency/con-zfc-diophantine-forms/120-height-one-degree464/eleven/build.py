#!/usr/bin/env python3
"""Construct the two new eleven-integer polynomials.

The arithmetic front end and DAG writer are adapted from the credited
incoming Coprime Projection construction. The new changes are proved
in PROOF.md. No proof search, variable exponent, or opaque norm
operation is used in the exported polynomials.
"""
import json
from pathlib import Path
import circuit as base

ROOT = Path(__file__).resolve().parent
VARS = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']


def build(centered=True):
    d = base.DAG(VARS)
    x = {v: d.leaf('variable', v) for v in VARS}
    p = {v: d.leaf('coefficient', v) for v in base.BASE_PORTS}
    J = 6*x['j']+1
    qm = p['beta']*J
    q = qm+1
    q2 = q*q
    q3 = q2*q
    W = 12*x['w']+4
    X = q*W
    Y = (2*x['v']+1)*q3
    E = X*Y
    a = E+Y
    H = 4*a+3
    Delta = a*a+H
    F = (p['K0']+W)*x['C']-x['z']*qm
    R = (q*(q-F)-x['C'])*(q2-1)+(p['MC']+q*p['MF'])*J
    k = R+1+x['h']*E
    c = x['c']
    c2 = c*c
    eta = c-Y*k
    U = p['cone_A']*F
    Vc = p['cone_B']*x['C']
    Derr = (U-q)**2+(Vc-q)**2
    Budget = k*k*(q2-Derr)-4*q2*eta*eta
    ell = E*Y
    L = ell*k
    Dt = 1+L*(L+k)
    D = 3*Budget-4
    Dg = 1+D*Dt*(x['s']*x['s'])
    I = 2*x['r']*c2
    I2 = I*I
    strong = Delta*I2
    Df = strong+1
    Q = Delta*strong
    delta = Q-1
    bfront = c-R+4*I*x['T']
    V = Df*bfront-c
    Cy = Q*V*V-1
    Da = delta*Cy
    K = X*(3*c-2*X)+2
    H2 = H*H
    H3 = H2*H
    S = x['s']*x['r']*H
    S2 = S*S
    zc = H*x['T']+K
    zc2 = zc*zc
    Ac = (zc2+3*H2)*(zc2*zc-19*H3)
    shift = Q*V if centered else 0
    Z = S*(x['n']+shift)-Ac
    P = Dt*Dg
    u = 4*S2*Df
    b = S2*Da
    e = 16*S2*P
    Z2 = Z*Z
    ub_sum = u+b
    ub_product = u*b
    vnorm = Z2-ub_sum-e
    ynorm = vnorm*vnorm-4*(ub_product+e*ub_sum)
    output = ynorm*ynorm-64*ub_product*e*Z2
    registers = {key: value for key, value in locals().copy().items()
                 if isinstance(value, base.Expr)}
    name = 'powered_coprime11_aux' if centered else 'powered_coprime11_direct'
    packet = base.export(name, d, output, registers,
                         dict(semantic_proof='PROOF.md', centered=centered))
    packet['coefficient_binding'] = 'coefficients/BINDING.json'
    packet['exact_degree'] = 464 if centered else 488
    degrees = []
    for row in packet['nodes']:
        if row[0] in ('add', 'sub', 'mul'):
            degrees.append(degrees[row[1]]+degrees[row[2]] if row[0] == 'mul'
                           else max(degrees[row[1]], degrees[row[2]]))
        else:
            degrees.append(int(row[0] == 'variable'))
    packet['syntactic_degree_bound'] = degrees[packet['output']]
    packet['register_degree_bounds'] = {
        key: degrees[index] for key, index in packet['named_registers'].items()}
    return packet


def main():
    packets = [build(False), build(True)]
    for packet in packets:
        (ROOT/(packet['name']+'.json')).write_text(json.dumps(packet, indent=2)+'\n')
    metrics = [{key: p[key] for key in ['name', 'variable_count', 'operations',
                'operation_counts', 'exact_degree', 'syntactic_degree_bound']}
               for p in packets]
    (ROOT/'METRICS.json').write_text(json.dumps(metrics, indent=2)+'\n')
    print(json.dumps(metrics, indent=2))


if __name__ == '__main__':
    main()
