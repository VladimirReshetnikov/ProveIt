#!/usr/bin/env python3
"""Exact cut degree and independently written front-end diagnostics."""
from pathlib import Path
import json
import random
import sys
import hashlib

HERE = Path(__file__).resolve().parent
SOURCE = HERE/'upstream/con-zfc-root-fusion-2026-10-24'
sys.path.insert(0, str(SOURCE/'verification'))
sys.path.insert(0, str(SOURCE))
from exact_polynomial import Ring
from check_integrated import (coefficients, Fp, formal_conjugate_norm,
                              evaluate_dag, require)
from build_reanchored import build


def degree():
    ring = Ring(['U','s','V','d','A','B','e','delta'])
    U,s,V,d,A,B,e,D = [ring.var(n) for n in ring.names]
    Z = U*V+s
    Cn = U*U*((D+1)*V*V-1)
    J = [D*(Z*Z+d+e-A-B)-Cn, 2*D*Z, 2*D*Z, 2*D]
    def multiply(left, right):
        result = [ring.scalar(0) for _ in range(4)]
        for i in range(4):
            for j in range(4):
                term = left[i]*right[j]
                if i&j&1:
                    term = term*d
                if i&j&2:
                    term = term*e
                result[i^j] = result[i^j]+term
        return result
    K = multiply(J,J)
    K[0] = K[0]-4*(D*D*A*B+D*Cn*(A+B))
    f = multiply(K,K)
    X2 = [Z*Z+d+e, 2*Z, 2*Z, ring.scalar(2)]
    f = [value-64*D**3*A*B*Cn*X2[i] for i,value in enumerate(f)]
    weights = [6,11,19,22,26,34,40,22]
    offsets = [0,11,20,31]
    component_degrees = [[p.weighted_degree(weights)+offsets[i]
                          for i,p in enumerate(parts)] for parts in (J,K,f)]
    require(f[0].homogeneous(weights,268)=={(4,0,4,0,0,0,2,4):16},
            'unique top scalar of the inner cleared norm')
    require(component_degrees[2][0]==268 and
            max(component_degrees[2][1:])<268,
            'all non-scalar components have strictly smaller weighted degree')
    lead = Ring(['j','w','v','h','r','c','z','C','beta'])
    j,w,v,h,r,c,z,C,beta = [lead.var(n) for n in lead.names]
    q0 = 6*beta*j
    a0 = 12*w*v*q0**2
    i0 = 2*r
    R0 = q0**4*z-12*q0**3*w*C
    k0 = R0+h*a0
    eta0 = -q0*v*k0
    top = 2**112*q0**64*a0**128*i0**64*c**128*R0**16*eta0**32
    monomial = (480,160,192,32,64,128,16,0,480)
    require(top.terms.get(monomial)==2**976*3**640,
            'selected specialized leading coefficient')
    require(top.weighted_degree((1,1,1,1,1,1,1,1,0))==1072,
            'total degree of the explicit top component')
    return dict(component_degrees=component_degrees, degree=1072,
                leading_form='2^16*Q0^16*Z0^16*e0^8',
                selected_monomial='j^480*w^160*v^192*h^32*r^64*c^128*z^16',
                selected_coefficient='2^976*3^640*beta^480')


def independent_front(inputs, ports, prime):
    x = {n:Fp(v,prime) for n,v in inputs.items()}
    p = {n:Fp(v,prime) for n,v in ports.items()}
    J = 1+6*x['j']; q = 1+p['beta']*J; W = 4*(3*x['w']+1)
    X = W*q; Y = x['v']*q; a = (X+1)*Y; E = a-Y
    H = 4*a+3; Delta = (a+1)*(a+3)
    C = x['C']; F = p['K0']*C+W*C-x['z']*q+x['z']; alpha = q-C-F
    R = ((q-1)*(q-F)+alpha)*(q*q-1)+(p['MC']+p['MF']*q)*J
    k = R+1+x['h']*E; c = x['c']; eta = c-Y*k; zeta = (Y+1)*k-c
    I = (2*x['r']+1)*c*c; I2 = I*I; Bstrong = Delta*I2
    Df = (a+2)**2*I2-I2+1; Q = (Delta*I)**2; delta = Q-1
    V = Df*c*x['T']-Df*R-c; Cy = (delta+1)*V*V-1
    ell0 = X*Y*Y; L = ell0*k
    Dtau = L*L+L*k+1; Dmain = 1+Delta*c*c; b0 = a*c+X
    coneU = p['cone_A']*F; coneZ = p['cone_B']*C
    G = coneU*coneZ-(coneU+coneZ-q)**2; Peta = eta*zeta
    scaled_G = x['v']*x['v']*G
    Pair = scaled_G*Peta-(scaled_G+Peta-1-x['t']**2)**2
    Ag = Pair-(1+x['p2']**2+x['p3']**2+x['p3'])
    M = 2*q*q; Lcrt = 4*H+1; U = M*H; ML = M*Lcrt
    center = M*(H*(x['n']+V)+Lcrt*b0)+H*(x['v']-q*q)
    return {n:v.value for n,v in locals().copy().items() if isinstance(v,Fp)}


def diagnostic(packet, ports):
    rng = random.Random(1072)
    primes = (1000000007, 1000000009, 1000000033)
    checked = 0
    while checked<45:
        prime = primes[checked%len(primes)]
        inputs = {name:rng.randrange(-30,31) for name in packet['variables']}
        if checked==0: inputs['v']=0
        if checked==1: inputs['c']=0
        if checked==2: inputs['v']=inputs['c']=0
        r = independent_front(inputs,ports,prime)
        if not r['delta']:
            continue
        actual = evaluate_dag(packet,inputs,ports,prime)
        for name,value in r.items():
            if name in packet['named_registers']:
                require(actual[packet['named_registers'][name]]==value,
                        'independent front '+name)
        dy = r['Cy']*pow(r['delta'],prime-2,prime)%prime
        radicands = [r['ML']**2*r['Dmain']%prime,
                     r['U']**2*r['Df']%prime,
                     r['U']**2*r['Dtau']%prime,
                     r['U']**2*r['Ag']%prime,
                     r['U']**2*dy%prime]
        target = pow(r['delta'],16,prime)*formal_conjugate_norm(
            r['center'],radicands,prime)%prime
        require(actual[packet['output']]==target, 'formal conjugate-product check')
        checked += 1
    return dict(samples=checked,primes=primes,
                scope='finite transcription diagnostics, not universal proofs')


def main():
    pins = json.loads((HERE/'SOURCE_PINS.json').read_text())
    manifest_bytes = (SOURCE/'MANIFEST.json').read_bytes()
    require(hashlib.sha256(manifest_bytes).hexdigest()==pins['manifest_sha256'],
            'pinned complete upstream manifest')
    inherited = json.loads(manifest_bytes)['files']
    for entry in inherited:
        payload = (SOURCE/entry['path']).read_bytes()
        require(len(payload)==entry['bytes'], 'inherited length '+entry['path'])
        require(hashlib.sha256(payload).hexdigest()==entry['sha256'],
                'inherited SHA256 '+entry['path'])
    packet = json.loads((HERE/'equation.json').read_text())
    require(packet==build(), 'literal graph rebuild')
    require(packet['variable_count']==13, 'variable count')
    require(packet['operations']==195, 'operation count')
    ports,binding = coefficients(SOURCE)
    receipt = dict(status='PASS', degree=degree(),
                   diagnostics=diagnostic(packet,ports), coefficients=binding,
                   authenticated_inherited_files=len(inherited),
                   variables=13,operations=195,
                   literal_sha256=hashlib.sha256((HERE/'equation.json').read_bytes()).hexdigest())
    (HERE/'AUDIT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in
        ('status','degree','diagnostics','variables','operations','literal_sha256')},indent=2))


if __name__=='__main__':
    main()
