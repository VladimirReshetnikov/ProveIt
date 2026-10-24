#!/usr/bin/env python3
"""Small guard-placement improvement to the pinned CRT five-radical norm.

No inherited file is modified. The upstream directory is an unmodified
extraction of ConZFC_13_Integer_Norms_2026-10-24.zip.
"""
from pathlib import Path
import json
import sys

HERE = Path(__file__).resolve().parent
SOURCE = HERE
sys.path.insert(0, str(SOURCE))
from build_equations import DAG, Expr, VARS13, BASE_PORTS, export
from five_square_norm import cleared_norm5


def build():
    d = DAG(VARS13)
    x = {name: d.leaf('variable', name) for name in VARS13}
    p = {name: d.leaf('coefficient', name) for name in BASE_PORTS}
    J = 6*x['j']+1
    q = p['beta']*J+1
    W = 12*x['w']+4
    X = q*W
    Y = q*x['v']
    E = X*Y
    a = E+Y
    H = 4*a+3
    Delta = a*a+H
    C = x['C']
    F = (p['K0']+W)*C-x['z']*(q-1)
    alpha = q-F-C
    R = (q*(q-F)-C)*(q*q-1)+(p['MC']+q*p['MF'])*J
    k = R+1+x['h']*E
    c = x['c']
    eta = c-Y*k
    zeta = k-eta
    c2 = c*c
    I = (2*x['r']+1)*c2
    I2 = I*I
    Bstrong = Delta*I2
    Df = 1+Bstrong
    Q = Delta*Bstrong
    delta = Q-1
    V = Df*(c*x['T']-R)-c
    Cy = Q*V*V-1
    ell0 = E*Y
    L = ell0*k
    Dtau = ell0*(ell0+1)*(k*k)+1
    Dmain = 1+Delta*c2
    b0 = X+a*c
    coneU = p['cone_A']*F
    coneZ = p['cone_B']*C
    G = coneU*coneZ-(q-coneU-coneZ)**2
    Peta = eta*zeta
    scaled_G = x['v']**2*G
    Pair = scaled_G*Peta-(x['t']**2-scaled_G-Peta+1)**2
    Ag = Pair-1-x['p2']**2-x['p3']*(x['p3']+1)
    M = 2*(q*q)
    Lcrt = 4*H+1
    U = M*H
    ML = 4*U+M
    U2 = U*U
    center = U*(x['n']+V)+ML*b0+H*(x['v']-q*q)
    scaled_Df = U2*Df
    scaled_Dtau = U2*Dtau
    scaled_Dmain = ML*ML*Dmain
    scaled_Ag = U2*Ag
    scaled_Cy = U2*Cy
    output = cleared_norm5(center, scaled_Df, scaled_Dtau, scaled_Dmain,
                          scaled_Ag, scaled_Cy, delta)
    registers = {name: value for name, value in locals().copy().items()
                 if isinstance(value, Expr)}
    packet = export('norm13_crt_guard_degree1072', d, output, registers,
                    dict(exact_degree=1072, norm_degree=32, crt_carrier=True,
                         degree_proof='PROOF.md', semantic_proof='PROOF.md'))
    packet['coefficient_binding'] = str(Path('upstream') /
        'con-zfc-root-fusion-2026-10-24/coefficients/BINDING.json')
    return packet


if __name__ == '__main__':
    packet = build()
    (HERE / 'equation.json').write_text(json.dumps(packet, indent=2)+'\n')
    print(json.dumps({k: packet[k] for k in
        ('name', 'variable_count', 'exact_degree', 'operations', 'operation_counts')},
        indent=2))
