#!/usr/bin/env python3
"""Independent exact audit of the 14-variable circuits.

Uses the independently authored sparse polynomial implementation from
quartic33.py. Checks the main-norm cancellation, root-elimination identities,
and complete highest homogeneous forms. No finite-field or random sampling
is needed for these checks. Does not verify compiler semantics or Pell facts.
"""
from collections import Counter
from pathlib import Path
import argparse
import json
from quartic33 import Poly, require

ROOT=Path(__file__).resolve().parent.parent


def abstract_identities():
    a,c,X,gamma,H=[Poly.var(n) for n in ['aa','cc','xx','gg','hh']]
    delta=a*a+H
    d=a*c+X+gamma*H
    rhs=2*a*c*(X+gamma*H)+(X+gamma*H)**2-H*c*c
    require(d*d-delta*c*c==rhs, 'independent main norm cancellation')
    P,Q,D,u,b,y,f,R=[Poly.var('abs_'+n) for n in ['P','Q','D','u','b','y','f','R']]
    A=Q*(D*u*u+b*b-y*y)+y*y-1
    B=2*Q*u*b
    E=f*f-D
    V=u*f-b-R*E
    aux=Q*V*V-(Q-1)*y*y
    correction=Q*(u*u-2*R*u*f+2*R*b+R*R*E)
    require(aux-1-A+B*f==E*correction,'independent auxiliary remainder')
    phi=P*(A*A-D*B*B+1)-1
    psi=(P*(A+1)-1)**2-D*(P*B)**2
    require(psi-P*phi==(P-1)*(2*P*A-1),'independent norm identity')
    require(D*B*B==4*(Q*D*u*u)*(Q*b*b),'independent cross-term factorization')
    return ['main norm cancellation','auxiliary remainder','outer/local norm identity','cross-term factorization']


def homogeneous_audit(packet):
    env={n:Poly.var(n) for n in packet['witnesses']}
    # Rename only the four constant symbols to the sparse package's
    # degree-zero coefficient ports. They remain algebraically independent.
    env.update(dict(Bm1=Poly.var('beta'),Kconstant=Poly.var('K0'),
                    MC=Poly.var('MC'),MF=Poly.var('MF')))
    def get(x):return Poly(x) if type(x) is int else env[x]
    counts=Counter()
    gate_names=[]
    for name,op,left,right in packet['source']:
        require(name not in env,'independent duplicate gate check')
        a,b=get(left),get(right)
        counts['M' if op=='*' else 'A']+=1
        if name=='norm_main':
            require([op,left,right]==['-','L15','Ac2'],'unexpected main norm gate')
            value=8*env['gamma']*env['R12']**2*env['R10a']
        elif op=='*':
            value=a*b
        elif a.degree()>b.degree():
            value=a
        elif a.degree()<b.degree():
            value=b if op=='+' else -b
        else:
            value=a+b if op=='+' else a-b
        require(bool(value.terms),'unexpected leading-form cancellation at '+name)
        env[name]=value
        gate_names.append(name)
    # Independent live-gate trace and port use.
    needed={packet['output']}
    for name,op,a,b in reversed(packet['source']):
        if name in needed:
            needed.update(x for x in [a,b] if type(x) is str)
    require(all(n in needed for n in gate_names),'dead gate in independent audit')
    require(all(n in needed for n in packet['witnesses']+packet['fixed_numerals']),'unused port')

    q=env['repunit']; k=env['R10b']; w=env['w']; s=env['s']
    i=env['i']; h=env['h']; gamma=env['gamma']; F=env['F']; alpha=env['alpha']
    z=env['transport_quotient']
    transport=w*(q-F-alpha)-z*q
    if packet['name']=='root14_product75':
        expected=8*gamma*h*i**12*k**27*w**21*s**48*q**177*(q-F)**4*transport
        degree=293
        monomial=(('Jrep',)*182+('h','gamma')+('i',)*12+('eta',)*27+
                  ('w',)*21+('s',)*48+('transport_quotient',)+('beta',)*182)
        expected_coefficient=-8
        ops=75
        adds=31
        leading_formula='8 gamma h i^12 k^27 w^21 s^48 q0^177 (q0-F)^4 [w(q0-F-alpha)-z q0]'
    else:
        expected=64*gamma**2*h**2*i**12*k**30*w**26*s**56*q**206*(q-F)**4*transport**2
        degree=342
        monomial=(('Jrep',)*212+('h',)*2+('gamma',)*2+('i',)*12+('eta',)*30+
                  ('w',)*26+('s',)*56+('transport_quotient',)*2+('beta',)*212)
        expected_coefficient=64
        ops=73
        adds=29
        leading_formula='64 gamma^2 h^2 i^12 k^30 w^26 s^56 q0^206 (q0-F)^4 [w(q0-F-alpha)-z q0]^2'
    actual=env[packet['output']]
    require(actual==expected,'full independent highest homogeneous form')
    require(actual.degree()==degree,'independent exact degree')
    require(actual.coefficient(monomial)==expected_coefficient,'uniform coefficient witness')
    require(len(gate_names)==ops and counts==dict(M=44,A=adds),'independent operation counts')
    return dict(variables=len(packet['witnesses']),operations=ops,multiplications=44,
        additions_subtractions=adds,exact_degree=degree,
        highest_homogeneous_form=leading_formula,
        leading_form_conventions='q0=beta Jrep; k=eta+zeta; z=transport_quotient',
        coefficient_witness={'monomial':dict(Counter(v for v in monomial if v!='beta')),
            'coefficient':f'{expected_coefficient} beta^{monomial.count("beta")}'},
        all_gates_live=True,all_ports_live=True)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    identities=abstract_identities()
    circuits={}
    for name in ['root14_product75','root14_outer73']:
        packet=json.loads((ROOT/'data'/(name+'.json')).read_text())
        circuits[name]=homogeneous_audit(packet)
    result=dict(status='PASS',exact_identities=identities,circuits=circuits,
        scope='Exact identities, all-integer highest forms, and operation counts only; inherited semantic theorems are not formally checked here.')
    path=ROOT/'data'/'root14_independent_checks.json'
    if args.write:
        path.write_text(json.dumps(result,indent=2)+'\n')
    else:
        require(json.loads(path.read_text())==result,'independent root audit artifact differs')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
