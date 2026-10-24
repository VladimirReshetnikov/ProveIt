#!/usr/bin/env python3
"""Trace-first thirteen-integer polynomial, exact degree 1072, 190 gates.

Uses the authenticated root-fusion package as a source of the small DAG and
norm primitives. No source main routine is run and no proof search occurs.
Run with --base PATH_TO_ROOT_FUSION_PACKAGE --out OUTPUT_DIRECTORY.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import importlib.util
import json
import random
import sys

PINS = {
    'build_equations.py': '1e6078132dd83e2607c49d453425d389b7853175f5a5a287333943509c2d5889',
    'five_square_norm.py': '9e8ed600620e7971f24ddb54df7e5f7f6e31777cbcd1920af7e3fea5b97f318d',
    'verification/exact_polynomial.py': 'f36b5a2cd966152f2ed0434705a813ac4f4f7a2243e798c74e4e0d1551dc508d',
    'verification/check_integrated.py': 'c13572f5c641925e2f8c04a11f71097017f330ebe4595da53f7f232cb4c4627b',
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load_dependencies(base):
    for path, expected in PINS.items():
        require(hashlib.sha256((base/path).read_bytes()).hexdigest() == expected,
                'authenticated source: '+path)
    sys.path.insert(0, str(base/'verification'))
    sys.path.insert(0, str(base))
    import build_equations as builder
    from five_square_norm import cleared_norm5
    from exact_polynomial import Ring
    import check_integrated as audit
    return builder, cleared_norm5, Ring, audit


def build(builder, cleared_norm5):
    d = builder.DAG(builder.VARS13)
    x = {name: d.leaf('variable', name) for name in builder.VARS13}
    p = {name: d.leaf('coefficient', name) for name in builder.BASE_PORTS}
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
    # Established exact first-norm factorization, one fewer live gate.
    Dtau = L*(L+k)+1
    Dmain = 1+Delta*c2
    b0 = X+a*c
    coneU = p['cone_A']*F
    coneZ = p['cone_B']*C
    G = coneU*coneZ-(q-coneU-coneZ)**2
    Peta = eta*zeta
    Pair = G*Peta-(x['t']**2-G-Peta+1)**2
    # New: no v^2 multiplier. The trace recovers the odd scale first.
    Ag = Pair-1-x['p2']**2-x['p3']*(x['p3']+1)
    M = 2*(q*q)
    U = M*H
    U2 = U*U
    # New: no Lambda enlargement of the main radical.
    center = U*(x['n']+V)+M*b0+H*(x['v']-q*q)
    scaled_Df = U2*Df
    scaled_Dtau = U2*Dtau
    scaled_Dmain = M*M*Dmain
    scaled_Ag = U2*Ag
    scaled_Cy = U2*Cy
    output = cleared_norm5(center, scaled_Df, scaled_Dtau,
                           scaled_Dmain, scaled_Ag, scaled_Cy, delta)
    registers = {name: val for name, val in locals().copy().items()
                 if isinstance(val, builder.Expr)}
    packet = builder.export('trace13_degree1072', d, output, registers, {
        'exact_degree': 1072,
        'norm_degree': 32,
        'trace_first_carrier': True,
        'degree_proof': 'Trace13 proof: weighted component degrees 268,250,263,255, followed by two quadratic norms.',
        'semantic_proof': '../proofs/TRACE13_PROOF.md',
        'source_pin': PINS,
        'inherited_calibration': 'The complete original six-port normalized integer kernel and its named ordinary native/K215 calibration.',
        'formalization_status': 'Ordinary mathematical proof; no new Lean or encoded object-ZFC certificate.',
    })
    packet['coefficient_binding'] = '../inherited/root_fusion/coefficients/BINDING.json'
    require(packet['operations'] == 190, 'expected 190 paid arithmetic operations')
    return packet


def exact_degree(Ring):
    ring = Ring(['U', 's', 'V', 'd', 'A', 'B', 'e', 'delta'])
    U,s,V,d,A,B,e,D = [ring.var(n) for n in ring.names]
    Z = U*V+s
    Cn = U*U*((D+1)*V*V-1)
    J = [D*(Z*Z+d+e-A-B)-Cn, 2*D*Z, 2*D*Z, 2*D]

    def multiply(left, right):
        out = [ring.scalar(0) for _ in range(4)]
        for i in range(4):
            for j in range(4):
                term = left[i]*right[j]
                if i&j&1: term = term*d
                if i&j&2: term = term*e
                out[i^j] = out[i^j]+term
        return out

    K = multiply(J,J)
    K[0] = K[0]-4*(D*D*A*B+D*Cn*(A+B))
    f = multiply(K,K)
    X2 = [Z*Z+d+e, 2*Z, 2*Z, ring.scalar(2)]
    f = [value-64*D**3*A*B*Cn*X2[i] for i,value in enumerate(f)]
    weights = [6,7,19,14,26,34,40,22]
    offsets = [0,7,20,27]
    degrees = [[value.weighted_degree(weights)+offsets[i]
                for i,value in enumerate(parts)] for parts in (J,K,f)]
    require(degrees == [[62,54,67,49],[134,116,129,121],[268,250,263,255]],
            'exact biquadratic component degrees')
    require(f[0].homogeneous(weights,268) == {(4,0,4,0,0,0,2,4):16},
            'unique highest scalar of the cleared inner norm')

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
    require(top.terms.get(monomial) == 2**976*3**640,
            'selected nonzero leading coefficient')
    require(top.weighted_degree((1,1,1,1,1,1,1,1,0)) == 1072,
            'exact specialized polynomial total degree')

    ring = Ring(['M','H','b','n','V','v','q','ell','k'])
    M,H,b,n,V,v,q,ell,k = [ring.var(nm) for nm in ring.names]
    center = M*H*(n+V)+M*b+H*(v-q*q)
    require(not (center-(M*(H*(n+V)+b)+H*(v-q*q))).terms,
            'mod-M carrier identity')
    require(not (center-(H*(M*(n+V)+v-q*q)+M*b)).terms,
            'mod-H carrier identity')
    require(not ((ell*k)*(ell*k+k)-ell*(ell+1)*k*k).terms,
            'factored first norm is an all-integer identity')
    return {
        'degree':1072,
        'weights':weights,
        'root_offsets':offsets,
        'component_degrees':degrees,
        'cleared_inner_norm_top':'16*delta^4*U^4*V^4*e^2',
        'full_norm_top':'2^16*Q0^16*Z0^16*e0^8',
        'expanded_front_top':'2^112*q0^64*a0^128*i0^64*c^128*R0^16*eta0^32',
        'selected_monomial':'j^480*w^160*v^192*h^32*r^64*c^128*z^16',
        'selected_coefficient':'2^976*3^640*beta^480',
        'leading_front_terms':len(top.terms),
        'exact_carrier_identities':2,
        'exact_first_norm_identity':True,
    }


def check_structure(packet):
    nodes = packet['nodes']
    counts = Counter()
    variables = set()
    ports = set()
    for i,node in enumerate(nodes):
        tag = node[0]
        if tag in ('add','sub','mul'):
            require(len(node) == 3 and all(type(j) is int and 0 <= j < i for j in node[1:]),
                    'topological binary arithmetic node')
            counts[tag] += 1
        else:
            require(tag in ('integer','variable','coefficient') and len(node) == 2,
                    'declared leaf kind')
            if tag == 'integer': require(type(node[1]) is int, 'integer numeral leaf')
            if tag == 'variable': variables.add(node[1])
            if tag == 'coefficient': ports.add(node[1])
    live = set()
    def visit(i):
        if i in live: return
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):
            visit(nodes[i][1]); visit(nodes[i][2])
    visit(packet['output'])
    require(len(live) == len(nodes), 'every exported node live')
    require(variables == set(packet['variables']) and len(variables) == 13,
            'exactly thirteen live integer coordinates')
    require(ports == {'beta','K0','MC','MF','cone_A','cone_B'}, 'whole six-port tuple')
    require(dict(counts) == packet['operation_counts'] and sum(counts.values()) == 190,
            'literal live operation census')
    return {'variable_count':13,'operations':190,'counts':dict(counts),
            'all_nodes_live':True,'all_six_coefficients_live':True}


def independent_front(inputs, ports, prime, Fp):
    x = {n:Fp(v,prime) for n,v in inputs.items()}
    p = {n:Fp(v,prime) for n,v in ports.items()}
    J = 1+6*x['j']; q = 1+p['beta']*J; W = 4*(3*x['w']+1)
    X = W*q; Y = x['v']*q; a = (X+1)*Y; E = a-Y
    H = 4*a+3; Delta = (a+1)*(a+3)
    C = x['C']; F = p['K0']*C+W*C-x['z']*q+x['z']; alpha=q-C-F
    R = ((q-1)*(q-F)+alpha)*(q*q-1)+(p['MC']+p['MF']*q)*J
    k = R+1+x['h']*E; c=x['c']; eta=c-Y*k; zeta=(Y+1)*k-c
    I=(2*x['r']+1)*c*c; I2=I*I; Bstrong=Delta*I2
    Df=(a+2)**2*I2-I2+1; Q=(Delta*I)**2; delta=Q-1
    V=Df*c*x['T']-Df*R-c; Cy=(delta+1)*V*V-1
    ell0=X*Y*Y; L=ell0*k; Dtau=1+ell0*(ell0+1)*k*k
    Dmain=1+Delta*c*c; b0=a*c+X
    coneU=p['cone_A']*F; coneZ=p['cone_B']*C
    G=coneU*coneZ-(coneU+coneZ-q)**2; Peta=eta*zeta
    Pair=G*Peta-(G+Peta-1-x['t']**2)**2
    Ag=Pair-(1+x['p2']**2+x['p3']**2+x['p3'])
    M=2*q*q; U=M*H; U2=U*U
    center=M*(H*(x['n']+V)+b0)+H*(x['v']-q*q)
    return {name:value.value for name,value in locals().copy().items() if isinstance(value,Fp)}


def transcription(packet, ports, audit):
    rng=random.Random(1072)
    primes=(1000000007,1000000009,1000000033)
    count=0; register_checks=0
    while count < 45:
        prime=primes[count%3]
        inputs={n:rng.randrange(-30,31) for n in packet['variables']}
        if count == 0: inputs['v']=0
        if count == 1: inputs['c']=0
        if count == 2: inputs['v']=inputs['c']=0
        r=independent_front(inputs,ports,prime,audit.Fp)
        if not r['delta']: continue
        values=audit.evaluate_dag(packet,inputs,ports,prime)
        for name,value in r.items():
            if name in packet['named_registers']:
                require(values[packet['named_registers'][name]] == value,
                        'independent front-end register: '+name)
                register_checks += 1
        dy=r['Cy']*pow(r['delta'],prime-2,prime)%prime
        radicands=[r['M']**2*r['Dmain']%prime,r['U']**2*r['Df']%prime,
                   r['U']**2*r['Dtau']%prime,r['U']**2*r['Ag']%prime,
                   r['U']**2*dy%prime]
        expected=(pow(r['delta'],16,prime)*
                  audit.formal_conjugate_norm(r['center'],radicands,prime))%prime
        require(values[packet['output']] == expected, 'literal 32-conjugate product diagnostic')
        count += 1
    return {'modular_trials':45,'primes':list(primes),
            'front_register_comparisons':register_checks,
            'exceptional_slices':['v=0','c=0','v=c=0'],
            'scope':'Finite transcription diagnostics, not a substitute for the semantic proof.'}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--base',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    base=args.base.resolve(); out=args.out.resolve(); out.mkdir(parents=True,exist_ok=True)
    builder,norm,Ring,audit=load_dependencies(base)
    packet=build(builder,norm)
    ports,coefficient_receipt=audit.coefficients(base)
    receipt={'status':'PASS','source_pins':PINS,
             'structure':check_structure(packet),
             'degree':exact_degree(Ring),
             'actual_fixed_coefficients':coefficient_receipt,
             'transcription':transcription(packet,ports,audit),
             'proof_boundary':'TRACE13_PROOF.md supplies the new unbounded trace/CRT argument. Native/compiler calibration is inherited. No consistency assumption and no new kernel/object-ZFC certificate.'}
    raw=(json.dumps(packet,indent=2)+'\n').encode()
    (out/'trace13_degree1072.json').write_bytes(raw)
    receipt['equation_sha256']=hashlib.sha256(raw).hexdigest()
    suffix='_OPTIMIZED' if not __debug__ else ''
    (out/('TRACE13_CHECKS'+suffix+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
