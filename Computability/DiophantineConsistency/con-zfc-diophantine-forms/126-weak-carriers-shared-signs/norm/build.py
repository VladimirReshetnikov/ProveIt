#!/usr/bin/env python3
"""Build eleven-integer polynomials with mixed or cubic carriers."""
import argparse
import json
from pathlib import Path
from dag import Graph, Expr

ROOT = Path(__file__).resolve().parent
VARIABLES = ['j','C','z','h','r','v','w','T','c','n','s']
PORTS = ['beta','K0','MC','MF','cone_A','cone_B']


def build(chart='mixed', centered=True):
    graph = Graph(VARIABLES)
    x = {v:graph.intern(('variable',v)) for v in VARIABLES}
    p = {v:graph.intern(('coefficient',v)) for v in PORTS}
    J = 6*x['j']+1
    qm = p['beta']*J
    q = qm+1
    q2 = q*q
    W = 12*x['w']+4
    X = q*W
    Y = q*x['v'] if chart == 'mixed' else (2*x['v']+1)*q2*q
    E = X*Y
    a = E+Y
    H = 4*a+3
    Delta = a*a+H
    F = (p['K0']+W)*x['C']-x['z']*qm
    R = (q*(q-F)-x['C'])*(q2-1)+(p['MC']+q*p['MF'])*J
    k = R+1+x['h']*E
    c = x['c']
    eta = c-Y*k
    error = (p['cone_A']*F-q)**2+(p['cone_B']*x['C']-q)**2
    budget = k*k*(q2-error)-4*q2*eta*eta
    ell = E*Y
    L = ell*k
    Dt = 1+L*(L+k)
    Dguard = 3*budget-4
    Dg = 1+Dguard*Dt*(x['s']*x['s'])
    P = Dt*Dg
    I = x['r']*(c*c)
    I2 = I*I
    strong = Delta*I2
    Df = 1+strong
    Q = Delta*strong
    delta = Q-1
    V = Df*(c-R+4*I*x['T'])-c
    Cy = Q*V*V-1
    Da = delta*Cy
    K = X*(3*c-2*X)+2
    if chart == 'mixed':
        M = 2*q2
        Dcarrier = M*H
        carrier = M*K+H*(x['v']-q2)
        zc = Dcarrier*x['T']+carrier
        M2 = M*M
        M4 = M2*M2
        S = x['s']*x['r']*M4*Dcarrier
    elif chart == 'cubic':
        Dcarrier = H
        zc = H*x['T']+K
        S = x['s']*x['r']*H
    else:
        raise ValueError(chart)
    Dc2 = Dcarrier*Dcarrier
    Dc3 = Dc2*Dcarrier
    zc2 = zc*zc
    obstruction = (zc2+3*Dc2)*(zc2*zc-19*Dc3)
    shift = 3*Q*V if centered else 0
    Z = S*(x['n']+shift)-obstruction
    S2 = S*S
    u = S2*Df
    b = 9*S2*Da
    e = 81*S2*P
    Z2 = Z*Z
    ub_sum = u+b
    ub = u*b
    wnorm = Z2-ub_sum-e
    inner = wnorm*wnorm-4*(ub+e*ub_sum)
    output = inner*inner-64*ub*e*Z2
    registers = {key:value for key,value in locals().items() if isinstance(value,Expr)}
    name = 'integer11_'+chart+('_centered' if centered else '_direct')
    result = graph.export(name,output,registers)
    result['chart'] = chart
    result['centered'] = centered
    result['exact_degree'] = ({'mixed':416,'cubic':464}[chart] if centered
                              else {'mixed':456,'cubic':488}[chart])
    result['semantic_proof'] = '../report.tex'
    degrees = []
    for row in result['nodes']:
        if row[0] == 'variable': deg = 1
        elif row[0] in ('integer','coefficient'): deg = 0
        elif row[0] == 'mul': deg = degrees[row[1]]+degrees[row[2]]
        else: deg = max(degrees[row[1]],degrees[row[2]])
        degrees.append(deg)
    result['syntactic_degree_bound'] = degrees[result['output']]
    result['register_degree_bounds'] = {k:degrees[i] for k,i in result['named_registers'].items()}
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir',type=Path,default=ROOT)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    metrics = []
    for chart in ['cubic','mixed']:
        for centered in [False,True]:
            packet = build(chart,centered)
            (args.output_dir/(packet['name']+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
            metrics.append({key:packet[key] for key in ['name','variable_count','operations',
                              'operation_counts','exact_degree','syntactic_degree_bound']})
    (args.output_dir/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))


if __name__ == '__main__': main()
