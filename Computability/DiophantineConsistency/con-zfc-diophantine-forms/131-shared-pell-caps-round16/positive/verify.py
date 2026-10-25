"""Independent finite controls for four doubly saturated one-square equations.

Reads JSON and gzip payloads only. Does not import or execute source builders.
All checks remain active with python -O.
"""
import argparse
import collections
from fractions import Fraction
import gzip
import hashlib
import json
import math
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'single_square': (87, 436),
    'single_square_lean': (88, 380),
    'direct_single_square': (92, 384),
    'direct_single_square_lean': (93, 334),
}

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def validate(data):
    leaves = set(data['witnesses'] + data['fixed_numerals'])
    seen = set(leaves)
    rows = data['source']
    require(len(data['witnesses']) == 10, 'ten unknowns')
    require(len(rows) == EXPECTED[data['name']][0], 'operation count')
    require(data['operations'] == len(rows), 'claimed count')
    require(data['exact_degree'] == EXPECTED[data['name']][1], 'claimed degree')
    require(data['operation_breakdown'] == dict(collections.Counter(r[1] for r in rows)), 'operation breakdown')
    byname = {}
    for row in rows:
        require(len(row) == 4, 'row arity')
        name, op, a, b = row
        require(name not in seen and op in ['+', '-', '*'], 'register uniqueness/op')
        for value in [a, b]:
            require(type(value) is int or value in seen, 'topological input ' + str(value))
        seen.add(name)
        byname[name] = row
    live = {data['output']}
    for row in reversed(rows):
        if row[0] in live:
            live.update(x for x in row[2:] if type(x) is str)
    require(set(byname) | leaves == live, 'dead or missing inputs')

def evaluate(data, variables, ports, modulus=None):
    values = dict(ports, **variables)
    for name, op, a, b in data['source']:
        x, y = values[a] if type(a) is str else a, values[b] if type(b) is str else b
        v = x+y if op == '+' else x-y if op == '-' else x*y
        values[name] = v if modulus is None else v % modulus
    return values

def reference(v, p, direct=False, lean=False):
    J,F,alpha,i,T,Y,n,eta,zeta = (v[x] for x in ['J','F','alpha','i','T','Y','n','eta','zeta'])
    beta,K0,MC,MF = (p[x] for x in ['beta','K0','MC','MF'])
    q=beta*J+1; C=q-F-alpha; mu=q*q+1
    X=q+v['x'] if direct else q*v['w']
    h=q*(q-1) if direct else q-1
    B=(q*K0+X)*C-q*F if direct else (K0+v['w'])*C-F
    P=q**(4 if direct else 3)*(q-1)
    low=h*Y-q**3*B-((q-1)*X if direct else 0)
    A=mu*Y*(X+1)+1; Delta=A*A-1; H=4*A-5
    k=eta+zeta; c=k*Y+eta; Vfirst=X*mu*mu*Y*Y
    D=1+Vfirst*(Vfirst+1)*k*k
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    e=k-R-1; Kc=1+Delta*c*c; E=i*c*c*A*Kc
    Df=1+Delta*D*E*E; Q=Delta*Delta*D*E*E; delta=Q-1
    b=c*(T+alpha)-R; V=Df*b-c; Dnum=Q*V*V-1
    G=D*Df; Kpos=X*(3*c-2*X)+2; M=P*mu*mu*H
    L=Delta*D*E*Df*b if lean else V*V
    Z=P*mu*mu*(H*(n-L*B)+Kpos)+H*(mu*mu*low-P*e)
    N=delta*Z*Z-M*M*G*Dnum
    return dict(q=q,C=C,mu=mu,X=X,Hp=H,k=k,c=c,V0=Vfirst,Dtau=D,R=R,e=e,
                Kc=Kc,U=E,Delta=Delta,Df=Df,Q=Q,delta=delta,cTR=b,V=V,
                Dnum=Dnum,Dg=G,Kpos=Kpos,Mtot=M,Znum=Z,N=N,L=L,B=B,h=h,P=P)

def polyadd(a,b,sign,p):
    c=[0]*max(len(a),len(b))
    for j,x in enumerate(a): c[j]=x
    for j,x in enumerate(b): c[j]=(c[j]+sign*x)%p
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def polymul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):
                if y: c[i+j]=(c[i+j]+x*y)%p
    while len(c)>1 and c[-1]==0: c.pop()
    return c

def polynomial_ray(data, ray, ports, p):
    values={x:[0,v%p] for x,v in ray.items()}
    values.update({x:[v%p] for x,v in ports.items()})
    for name,op,a,b in data['source']:
        aa=values[a] if type(a) is str else [a%p]
        bb=values[b] if type(b) is str else [b%p]
        values[name]=polymul(aa,bb,p) if op=='*' else polyadd(aa,bb,1 if op=='+' else -1,p)
    return values['N']

def predicted_top(v,p,direct,lean,modulus):
    q=p['beta']*v['J']; k=v['eta']+v['zeta']; X=q+v['x'] if direct else q*v['w']
    c=k*v['Y']; A=q*q*v['Y']*X; D=q**8*X*X*v['Y']**4*k*k
    E=v['i']*A**3*c**4; F=A*A*D*E*E; Q=A**4*D*E*E
    b=-q**3*(q-v['F']); V=F*b; M=4*q**(9 if direct else 8)*A
    B=(q*p['K0']+X)*(q-v['F']-v['alpha'])-q*v['F'] if direct else v['w']*(q-v['F']-v['alpha'])
    L=A*A*D*E*F*b if lean else V*V
    return (Q*M*M*L*L*B*B)%modulus

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--output',default='CHECK.json'); args=parser.parse_args()
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for filename,digest in pins['files'].items():
        require(hashlib.sha256((ROOT/filename).read_bytes()).hexdigest()==digest,'source pin '+filename)
    rng=random.Random(160087)
    payloads=None; artifacts=[]; definitions=0; raychecks=0
    for name,(ops,degree) in EXPECTED.items():
        data=json.loads((ROOT/'equations'/f'{name}.json').read_text()); validate(data)
        direct=name.startswith('direct_'); lean=name.endswith('_lean')
        actual={}
        for port,info in data['coefficient_binding']['ports'].items():
            blob=(ROOT/data['coefficient_binding']['path']/info['file']).read_bytes()
            raw=gzip.decompress(blob)
            require(hashlib.sha256(blob).hexdigest()==info['gzip_sha256'],'gzip binding')
            require(hashlib.sha256(raw).hexdigest()==info['raw_sha256'],'raw binding')
            value=int.from_bytes(raw,'little')
            require(value.bit_length()==info['bits'],'coefficient bit length')
            actual[port]=value
        if payloads is None: payloads={k:{'bits':v.bit_length()} for k,v in actual.items()}
        for trial in range(24):
            variables={x:rng.randint(1,8) for x in data['witnesses']}
            ports={'beta':31,'K0':43,'MC':13,'MF':37}
            got=evaluate(data,variables,ports); ref=reference(variables,ports,direct,lean)
            for key,value in ref.items():
                if key in got: require(got[key]==value,'literal definition '+name+' '+key)
            q=ref['q']; h=ref['h']; L=ref['L']; B=ref['B']
            normalized=Fraction(variables['n'])+Fraction(ref['Kpos'],ref['Hp'])+Fraction(variables['Y'],q**3)-Fraction((1+h*L)*B,h)-Fraction(ref['e'],ref['mu']**2)
            if direct: normalized-=Fraction(ref['X'],q**4)
            require(Fraction(ref['Znum'],ref['Mtot'])==normalized,'normalized carrier')
            require(math.gcd(ref['Dtau'],ref['Df']*ref['delta']*ref['Dnum'])==1,'D coprimality')
            require(math.gcd(ref['Df'],ref['delta']*ref['Dnum'])==1,'strong coprimality')
            definitions+=1
        for p in [2147483647,2305843009213693951]:
            ports={k:v%p for k,v in actual.items()}
            variables={x:rng.randint(1,7) for x in data['witnesses']}
            got=evaluate(data,variables,ports,p); ref=reference(variables,ports,direct,lean)
            require(got['N']==ref['N']%p,'actual-coefficient modular definition')
            polynomial=polynomial_ray(data,variables,ports,p)
            require(len(polynomial)-1==degree,'full polynomial degree')
            require(polynomial[-1]==predicted_top(variables,ports,direct,lean,p),'global top-form replay')
            raychecks+=1
        mutation=json.loads(json.dumps(data)); mutation['source'][0][2]='unknown'
        rejected=False
        try: validate(mutation)
        except RuntimeError: rejected=True
        require(rejected,'topology mutation accepted')
        artifacts.append({'name':name,'operations':ops,'degree':degree,'sha256':hashlib.sha256((ROOT/'equations'/f'{name}.json').read_bytes()).hexdigest()})
    gcdchecks=0; bounds=0
    for A in range(2,11):
        d=A*A-1
        for c in range(1,8):
            K=1+d*c*c
            for D in range(2,16):
                for i in range(1,4):
                    E=i*c*c*A*K; F=1+d*D*E*E; Q=d*d*D*E*E; delta=Q-1
                    for b in range(-3,4):
                        V=F*b-c; Dnum=Q*V*V-1
                        require(math.gcd(D,F*delta*Dnum)==1 and math.gcd(F,delta*Dnum)==1,'universal coprimality control')
                        gcdchecks+=1
                    if A>=7:
                        for b in [c+1,100*c+1]:
                            V=F*b-c; Dnum=Q*V*V-1; G=D*F
                            require(4*G*Dnum<delta*V**4,'V-square majorant margin')
                            L=d*D*E*F*b
                            require(4*G*Dnum<delta*L*L and L>2*b,'lean majorant margin')
                            bounds+=1
    result={'status':'passed','artifacts':artifacts,'bound_source_files':len(pins['files']),'definition_and_carrier_checks':definitions,
            'complete_modular_polynomial_replays':raychecks,'coprimality_controls':gcdchecks,
            'conditional_majorant_controls':bounds,'coefficient_payloads':payloads,
            'scope':'Finite transcription controls; unbounded semantics and attained global degree are proved in PROOF.md.'}
    target=Path(args.output); target=target if target.is_absolute() else ROOT/target
    target.write_text(json.dumps(result,indent=2)+'\n'); print(json.dumps(result,indent=2))

if __name__=='__main__': main()
