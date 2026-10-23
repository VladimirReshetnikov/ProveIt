#!/usr/bin/env python3
"""Finite checks for the deflated-majorant nine-variable equation.

No network access, third-party packages or consistency search. Numerical
comparisons check literal transcription; unbounded equivalence is in PROOF.md.
"""
from pathlib import Path
from collections import Counter
import gzip, hashlib, json, math, random, subprocess, sys
from build import build, degree_certificate, PORTS

ROOT = Path(__file__).resolve().parent

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def fixed_values_mod(body, ports, p):
    result = {}
    for record in body['coefficient_recipes']:
        result[record['name']] = sum(
            t['coefficient'] * math.prod(pow(ports[x] % p, k, p)
                for x, k in zip(PORTS, t['powers']))
            for t in record['terms']) % p
    result['base_scale'] = pow(2, body['base_scale_exponent'], p)
    result['threshold_scale'] = pow(2, body['threshold_scale_exponent'], p)
    return result

def evaluate(body, fixed, values, p):
    out = []
    for number, node in enumerate(body['nodes']):
        kind = node['kind']
        if kind == 'literal':
            r = node['value']
        elif kind == 'fixed':
            r = fixed[node['name']]
        elif kind == 'variable':
            r = values[node['name']]
        else:
            require(0 <= node['left'] < number and 0 <= node['right'] < number,
                    'topological operands')
            a, b = out[node['left']], out[node['right']]
            if kind == 'add': r = a+b
            elif kind == 'sub': r = a-b
            elif kind == 'mul': r = a*b
            else: raise ValueError('unsupported arithmetic operation')
        out.append(r % p)
    return out[body['output']], {name: out[k] for name,k in body['named_nodes'].items()}

def literal(values, ports, p):
    """Independent literal formula, without the construction's DAG helpers."""
    b,g,h,s,w,C,i,j,n = (values[k] for k in ('b','g','h','s','w','C','i','j','n'))
    B=pow(2,2134939,p)*b*b%p
    code=json.loads((ROOT/'data/split_code.json').read_text())
    kernels=json.loads((ROOT/'data/split_kernels.json').read_text())
    kd=[]
    for row in kernels['kernels']:
        z=0
        for term in row['terms']:
            coefficient=sum(t['coefficient']*math.prod(pow(ports[k]%p,ex,p)
                for k,ex in zip(PORTS,t['powers'])) for t in term['coefficient'])%p
            z=(z+coefficient*pow(B,term['exponent'],p))%p
        kd.append(z)
    D0,D1,D2=kd
    ell=sum(pow(B,x,p) for x in code['weights'])%p
    targets=sum(pow(B,x,p) for x in code['targets'])%p
    Us=(ell+g)%p;Gs=(D2*Us*Us+D1*Us+D0)%p
    N0=pow(B,117,p);mask=(N0-1-(b-1)*ell)%p
    Sc=(g+N0*(2*Gs+targets))%p
    Tc=(mask+N0*(B-2)*targets)%p
    L=b*pow(B,2279,p)%p
    R=(L*(Sc+Tc+1)-Sc-1)%p
    N=pow(2,17079501,p)*b*pow(B,1201,p)%p
    U=N*N*w%p;Y=N*N*s%p;M=R*Y%p
    P=2*M*M*U%p;K=(R+1+h*(P-1))%p
    A=M*(U+1)%p;B1=(2*R+1)%p;W1=b*w%p
    J=(4*A-5)%p;Q=(3*W1*C-2*(W1*W1-1))%p
    D=((A*A-1)*C*C+1)%p;e=i*J*C%p;E=e*D*C%p
    F=((A*A-1)*E*E+1)%p
    Lm=(C*D+1-A)%p;G=(A+F*Lm)%p
    H=(C+F*(B1+(j-1)*C))%p
    I=((G*G-1)*H*H+1)%p
    a0=((P*P-1)*K*K+1)%p;a1=4096**2*D*F*I%p
    t=b*pow(B,116,p)%p
    m=(K*K*(4*t-g)-16*t*(C-K*Y)**2)%p
    Ns=(2*G+Lm)%p
    N1=(2*e*e*D*(D-1)*Lm+3*C)%p
    N2=2*e*e*(D-1)*Lm%p
    N3=2*e*e*(Lm-C)%p;N4=2*e*e*C%p
    T=(e*((2048*D*D-1024*D-256)*Ns-128*N1-80*N2-56*N3-42*N4
        +i*i*(1568-448*A+288*C))+640*i+4096)%p
    V0=P*K%p;V1=T*H%p
    Omega=J*m%p;E0=(J*(n+W1*W1)+Q)%p
    theta=(E0-Omega*(V0+V1))%p
    value=((theta*theta-Omega*Omega*(a0+a1))**2-4*pow(Omega,4,p)*a0*a1)%p
    return value,D

def main():
    checks={}
    for file in ['check_source.py','check_exact.py']:
        result=subprocess.run([sys.executable,str(ROOT/file)],capture_output=True,text=True,check=True)
        checks[file]=json.loads(result.stdout)
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    raw_ports={}
    for r in binding['payloads']:
        gz=(ROOT/'coefficients'/r['path']).read_bytes();raw=gzip.decompress(gz)
        require(digest(gz)==r['gzip_sha256'] and digest(raw)==r['sha256'],'fixed tuple byte hash')
        z=int.from_bytes(raw,'little')
        require(len(raw)==r['bytes'] and z.bit_length()==r['bit_length'],'fixed tuple size')
        raw_ports[r['name']]=z
    ports={k:raw_ports[v] for k,v in binding['port_aliases'].items()}
    bodies={}
    for positive in [True,False]:
        label='order7_'+('positive' if positive else 'natural')
        for certificate in [False,True]:
            suffix='_certificate' if certificate else ''
            body=json.loads((ROOT/f'generated/{label}{suffix}.json').read_text())
            fresh=build('split_116',positive,certificate,'horner','binary')
            fresh['exact_degree']=body['exact_degree']
            require(json.loads(json.dumps(fresh))==body,'deterministic literal circuit rebuild')
            require(body['exact_degree']==(2322466 if certificate else 1573266),
                    'declared exact degree')
            counts=Counter(n['kind'] for n in body['nodes'] if n['kind'] in ('add','sub','mul'))
            require(dict(counts)==body['operation_counts'] and sum(counts.values())==body['total_operations'],'gate count')
            expected_cost=(1105 if positive else 1112) if certificate else (504 if positive else 511)
            require(body['total_operations']==expected_cost,'frozen primary/certificate operation count')
            live=set();todo=[body['output']]
            while todo:
                k=todo.pop()
                if k in live:continue
                live.add(k);node=body['nodes'][k]
                if node['kind'] in ('add','sub','mul'):todo.extend((node['left'],node['right']))
            require(len(live)==len(body['nodes']),'all graph nodes live')
            variables=[n['name'] for n in body['nodes'] if n['kind']=='variable']
            require(variables==body['variables'] and len(variables)==9,'nine ordered input variables')
            if certificate:
                degree=degree_certificate(body)
                require(degree['exact_degree']-20*degree['named_degrees']['D']==1573266,'exact degree deduction')
                require(degree['named_degrees']['major_Rnum']==187305,'remainder exact degree')
                require(degree['named_degrees']['deltaT10']==655559,'defect numerator exact degree')
                require(degree['named_degrees']['delta1_D10']-10*degree['named_degrees']['D']==598873,'radicand defect degree')
            bodies[positive,certificate]=body
    rng=random.Random(20261023);comparisons=0
    for modulus in [1000003,1000033,1000037]:
        fixed={key:fixed_values_mod(body,ports,modulus) for key,body in bodies.items()}
        for _ in range(40):
            positive_values={x:rng.randint(1,100) for x in bodies[True,False]['variables']}
            direct,D=literal(positive_values,ports,modulus)
            for key,body in bodies.items():
                pos,cert=key
                values=positive_values if pos else {k:v-1 for k,v in positive_values.items()}
                result,registers=evaluate(body,fixed[key],values,modulus)
                expected=direct*pow(D,20,modulus)%modulus if cert else direct
                require(result==expected,'independent literal/domain/certificate comparison')
                comparisons+=1
    result={'status':'PASS','positive_variables':9,'positive_operations':504,
            'natural_operations':511,'exact_degree':1573266,
            'fixed_payloads':4,'modular_literal_comparisons':comparisons,
            'component_checks':checks,'scope':'Finite data, arithmetic, exact identities and degree. Semantic equivalence is the mathematical theorem in PROOF.md with its named inherited dependencies.'}
    print(json.dumps(result,indent=2))
    (ROOT/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':
    main()
