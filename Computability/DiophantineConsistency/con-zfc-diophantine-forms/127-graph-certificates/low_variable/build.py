#!/usr/bin/env python3
"""Literal eleven-integer linear-multiplier polynomial circuits.

The graph utility is retained from the credited Weak_Carriers source.
All arithmetic here implements the definitions in PROOF.md.
"""
import argparse
import json
from pathlib import Path
from dag import Graph, Expr

ROOT = Path(__file__).resolve().parent
VARIABLES = ['j','C','z','h','r','v','w','T','c','n','s']
PORTS = ['beta','K0','MC','MF','cone_A','cone_B']

def build(centered=True):
    graph = Graph(VARIABLES)
    x = {v: graph.intern(('variable',v)) for v in VARIABLES}
    p = {v: graph.intern(('coefficient',v)) for v in PORTS}
    j,C,z,h,r,v,w,T,c,n,s = [x[v] for v in VARIABLES]
    J = 6*j+1
    qm = p['beta']*J
    q = qm+1
    q2 = q*q
    W = 12*w+4
    X = q*W
    Y = q*v
    E = X*Y
    a = E+Y
    H = 4*a+3
    Delta = a*a+H
    F = (p['K0']+W)*C-z*qm
    R = (q*(q-F)-C)*(q2-1)+(p['MC']+q*p['MF'])*J
    k = R+1+h*E
    c2 = c*c
    eta = c-Y*k
    error = (p['cone_A']*F-q)**2+(p['cone_B']*C-q)**2
    budget = k*k*(q2-error)-4*q2*eta*eta
    ell = E*Y
    L = ell*k
    Dt = 1+L*(L+k)
    D81 = 243*budget-324
    Dg81 = 81+D81*Dt*s*s
    P81 = Dt*Dg81
    U = r*c2
    I2 = U*c2
    strong = Delta*I2
    Df = 1+strong
    Q = Delta*strong
    delta = Q-1
    V = Df*(c-R+4*U*T)-c
    QV = Q*V
    Cy = QV*V-1
    Da = delta*Cy
    K = X*(3*c-2*X)+2
    M = 2*q2
    Dc = M*H
    M2 = M*M
    M4 = M2*M2
    S = s*r*M4*Dc
    Dc2 = Dc*Dc
    Dc3 = Dc2*Dc
    zc = Dc*T+M*K+H*(v-q2)
    zc2 = zc*zc
    Ac = (zc2+3*Dc2)*(zc2*zc-19*Dc3)
    Z = S*(n+QV)-Ac if centered else S*n-Ac
    S2 = S*S
    S2r = S2*r
    AA = 9*S2r*Df
    BB = S2*Da
    GG = S2r*r*P81
    Z2 = Z*Z
    paired = Z2+AA-BB-GG
    left = AA*Z2
    right = BB*GG
    inner = paired*paired-4*(left+right)
    output = inner*inner-64*left*right
    registers = {key:value for key,value in locals().items() if isinstance(value,Expr)}
    name = 'linear_multiplier11_'+('centered412' if centered else 'direct440')
    result = graph.export(name,output,registers)
    result['centered'] = centered
    result['exact_degree'] = 412 if centered else 440
    result['semantic_proof'] = 'PROOF.md'
    degrees=[]
    for row in result['nodes']:
        if row[0]=='variable': deg=1
        elif row[0] in ('integer','coefficient'): deg=0
        elif row[0]=='mul': deg=degrees[row[1]]+degrees[row[2]]
        else: deg=max(degrees[row[1]],degrees[row[2]])
        degrees.append(deg)
    result['syntactic_degree_bound']=degrees[result['output']]
    result['register_degree_bounds']={k:degrees[i] for k,i in result['named_registers'].items()}
    return result

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--output-dir',type=Path,default=ROOT)
    args=ap.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
    metrics=[]
    for centered in [False,True]:
        obj=build(centered)
        (args.output_dir/(obj['name']+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
        metrics.append({k:obj[k] for k in ['name','variable_count','operations','operation_counts','exact_degree','syntactic_degree_bound']})
    (args.output_dir/'METRICS.json').write_text(json.dumps(metrics,indent=2)+'\n')
    print(json.dumps(metrics,indent=2))

if __name__=='__main__': main()
