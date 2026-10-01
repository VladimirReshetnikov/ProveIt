"""A complete positive-coordinate Pell relation with computed Q=8**(32*x).

No packed-mask/AND premise, checksum, external exponent oracle or free
comparison is used. All supplied coordinates are positive integers.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import comb, prod
from pathlib import Path
import random

PARAMETERS = ['x']
AUXILIARIES = ['delta', 's', 'eta', 'zeta', 'g', 'gamma',
               'f', 'i', 'j', 'o', 'y', 'h']
FACTOR_NAMES = ['N0', 'N1', 'Ns', 'N3', 'Nk', 'Nl']


def build():
    source = []
    def put(name, op, a, b):
        source.append((name, op, a, b)); return name
    put('r_scaled', '*', 48, 'x')
    put('r', '+', 'r_scaled', 15)
    put('Q', '+', 'x', 'delta')
    put('X', '*', 2**31, 'Q')
    put('E', '*', 'X', 's')
    put('k', '+', 'eta', 'zeta')
    put('kY', '*', 'k', 's')
    put('c', '+', 'kY', 'eta')
    put('a', '+', 'E', 's')
    put('four_a', '*', 4, 'a')
    put('H', '+', 'four_a', 3)
    put('a2', '*', 'a', 'a')
    put('Delta', '+', 'a2', 'H')
    put('ac', '*', 'a', 'c')
    put('gammaH', '*', 'gamma', 'H')
    put('L', '+', 'X', 'gammaH')
    put('D', '+', 'L', 'ac')
    put('D2', '*', 'D', 'D')
    put('c2', '*', 'c', 'c')
    put('Delta_c2', '*', 'Delta', 'c2')
    put('N1', '-', 'D2', 'Delta_c2')
    put('g2', '*', 'g', 'g')
    put('first_base', '*', 'E', 'kY')
    put('g_minus_k', '-', 'g', 'k')
    put('first_cross', '*', 'first_base', 'g_minus_k')
    put('four_cross', '*', 4, 'first_cross')
    put('N0', '+', 'g2', 'four_cross')
    put('t', '*', 'i', 'c2')
    put('t2', '*', 't', 't')
    put('strong_Q', '*', 'Delta', 't2')
    put('f2', '*', 'f', 'f')
    put('Ns', '-', 'f2', 'strong_Q')
    put('aux_K', '*', 'Delta', 'strong_Q')
    put('of', '*', 'o', 'f')
    put('V', '-', 'of', 'c')
    put('V2', '*', 'V', 'V')
    put('y2', '*', 'y', 'y')
    put('aux_gap', '-', 'V2', 'y2')
    put('aux_product', '*', 'aux_K', 'aux_gap')
    put('N3', '+', 'aux_product', 'y2')
    put('hE', '*', 'h', 'E')
    put('K', '-', 'k', 'hE')
    put('Nk', '-', 'K', 'r')
    put('jc', '*', 'j', 'c')
    put('linear_gap', '-', 'V', 'jc')
    put('twice_K', '+', 'K', 'K')
    put('Nl', '+', 'linear_gap', 'twice_K')
    last = FACTOR_NAMES[0]
    for index, factor in enumerate(FACTOR_NAMES[1:], 1):
        last = put('factor_product_' + str(index), '*', last, factor)
    return dict(source=source, parameters=list(PARAMETERS), auxiliaries=list(AUXILIARIES),
                unit_factors=list(FACTOR_NAMES), unit_register=last,
                comparisons=[(last, 1)], interfaces=dict(input='x', power='Q', exponent='r'),
                positive_integer_domain=True,
                projection='Q=8^(32*x), x>=1; Q is a computed register')


def polynomial_source(packet=None, *, sum_of_squares=False):
    if packet is None: packet = build()
    assert packet == build(), 'only the literal canonical packet is accepted'
    source = list(packet['source'])
    source.append(('output', '-', packet['unit_register'], 1))
    output = 'output'
    if sum_of_squares:
        source.append(('output_square', '*', output, output)); output = 'output_square'
    return source, output


def execute(source, values):
    env = dict(values)
    def val(v): return env[v] if isinstance(v, str) else v
    for name, op, a, b in source:
        a, b = val(a), val(b)
        assert name not in env
        env[name] = a*b if op == '*' else a+b if op == '+' else a-b
    return env


def degrees(packet=None, *, sum_of_squares=False):
    if packet is None: packet = build()
    source, output = polynomial_source(packet, sum_of_squares=sum_of_squares)
    degree = {name: 1 for name in packet['parameters']+packet['auxiliaries']}
    get = lambda name: degree[name] if isinstance(name, str) else 0
    for name, op, a, b in source:
        degree[name] = get(a)+get(b) if op == '*' else max(get(a), get(b))
        if name == 'N1':
            # Exact all-integer cancellation: (L+ac)^2-(a²+H)c².
            degree[name] = max(2*degree['L'], degree['L']+degree['a']+degree['c'],
                               degree['H']+2*degree['c'])
    return degree, degree[output]


def ledger(packet=None, *, sum_of_squares=False):
    if packet is None: packet = build()
    source, _ = polynomial_source(packet, sum_of_squares=sum_of_squares)
    counts = Counter(row[1] for row in source)
    cert = Counter(row[1] for row in packet['source'])
    return dict(operations=len(source), multiplications=counts['*'],
        additions_subtractions=counts['+']+counts['-'], certificate=len(packet['source']),
        certificate_multiplications=cert['*'], certificate_additions=cert['+']+cert['-'],
        equations=1, witnesses=len(packet['auxiliaries']), parameters=len(packet['parameters']),
        degree_bound=degrees(packet, sum_of_squares=sum_of_squares)[1])


def factors(z):
    x=z['x']; r=48*x+15; Q=x+z['delta']; X=2**31*Q; Y=z['s']
    E=X*Y; k=z['eta']+z['zeta']; c=k*Y+z['eta']; a=E+Y
    H=4*a+3; Delta=a*a+H; D=X+a*c+z['gamma']*H
    t=z['i']*c*c; V=z['o']*z['f']-c; K=k-z['h']*E
    return dict(N0=z['g']**2+4*E*k*Y*(z['g']-k), N1=D*D-Delta*c*c,
                Ns=z['f']**2-Delta*t*t,
                N3=Delta*Delta*t*t*(V*V-z['y']**2)+z['y']**2,
                Nk=K-r, Nl=V-z['j']*c+2*K)


def pell(A, n, modulus=None):
    """Binary powering in Z[sqrt(A²-1)], exact even for large indices."""
    assert type(A) is int and A >= 2 and type(n) is int and n >= 0
    D=A*A-1
    def mul(u, v):
        a=u[0]*v[0]+D*u[1]*v[1]; b=u[0]*v[1]+u[1]*v[0]
        return (a,b) if modulus is None else (a % modulus, b % modulus)
    result=(1,0); base=(A,1)
    while n:
        if n & 1: result=mul(result,base)
        n >>= 1
        if n: base=mul(base,base)
    return result


def canonical_main(x):
    """Materialize only first/main coordinates, never the huge auxiliary index."""
    assert type(x) is int and x >= 1
    r=48*x+15; p=2*r+1; X=2**p; Q=2**(96*x)
    Y=(X+1)**(2*r)//X**r; E=X*Y; a=Y*(X+1); A=a+2; H=4*a+3
    D,c=pell(A,p); first,k=pell(2*X*Y*Y+1,r+1)
    def divide(a,b):
        q,rem=divmod(a,b); assert rem == 0; return q
    z=dict(x=x,delta=Q-x,s=Y,eta=c-k*Y,zeta=(Y+1)*k-c,
           g=first-2*X*Y*Y*k,gamma=divide(D-X-a*c,H),h=divide(k-r-1,E))
    assert min(z.values()) > 0
    assert Y.bit_length() > 0 and (Y & -Y).bit_length()-1 == r.bit_count()
    assert Y == sum(comb(2*r,r+j)*X**j for j in range(r+1))
    assert 0 < c-k*Y < k
    assert z['g']**2+4*E*k*Y*(z['g']-k) == 1
    assert D*D-(A*A-1)*c*c == 1
    assert k-z['h']*E-r == 1
    return dict(x=x,r=r,p=p,all_main_coordinates_positive=True,first_main_index_equalities=True,
                Q_bits=Q.bit_length(), Y_bits=Y.bit_length(), c_bits=c.bit_length(),
                first_index=r+1,main_index=p,Y_valuation=r.bit_count(),
                witness_bit_lengths={name:value.bit_length() for name,value in z.items()},
                scope='Actual main/first coordinates; normalized auxiliary coordinates not materialized.')


def canonical_auxiliary(A, p):
    assert type(p) is int and p >= 3 and p % 4 == 3
    Delta=A*A-1; c=pell(A,p)[1]; m=2*c*p; f,psi=pell(A,m)
    i,rem=divmod(psi,c*c); assert rem == 0 and i > 0
    T=Delta*psi; chi,y=pell(T,p); V,rem=divmod(chi,T); assert rem == 0
    o,rem=divmod(V+c,f); assert rem == 0
    j,rem=divmod(V+p,c); assert rem == 0
    assert min(f,i,j,o,y) > 0
    assert f*f-Delta*(i*c*c)**2 == 1
    assert T*T*(V*V-y*y)+y*y == 1
    assert V == o*f-c == j*c-p
    return dict(A=A,p=p,m=m,positive_five_coordinates=True,three_auxiliary_relations=True,
                bit_lengths={n:v.bit_length() for n,v in dict(f=f,i=i,j=j,o=o,y=y).items()},
                scope='Local normalized auxiliary block, not a full x>=1 gadget zero.')


def verify():
    import sympy as sp
    packet=build(); source,out=polynomial_source(packet); ss,so=polynomial_source(packet,sum_of_squares=True)
    for rows,target in ((source,out),(ss,so)):
        known=set(PARAMETERS+AUXILIARIES); parents={}
        for name,op,a,b in rows:
            assert name not in known and op in ('+','-','*')
            assert all(type(v) is int or v in known for v in (a,b))
            known.add(name); parents[name]=(a,b)
        seen=set(); stack=[target]
        while stack:
            v=stack.pop()
            if not isinstance(v,str) or v not in parents or v in seen: continue
            seen.add(v); stack.extend(parents[v])
        assert seen == set(parents)
        assert all(v in known for v in packet['interfaces'].values())
    z={n:sp.Symbol(n) for n in PARAMETERS+AUXILIARIES}
    env=execute(packet['source'],z); exact=factors(z)
    for name in FACTOR_NAMES: assert sp.expand(env[name]-exact[name]) == 0
    identity=env['L']**2+2*env['L']*env['a']*env['c']-env['H']*env['c']**2
    assert sp.expand(env['N1']-identity) == 0
    exact_degrees={n:sp.Poly(exact[n],*z.values()).total_degree() for n in FACTOR_NAMES}
    deg,bound=degrees(packet)
    assert exact_degrees == {n:deg[n] for n in FACTOR_NAMES}
    assert sum(exact_degrees.values()) == bound
    rng=random.Random(631175); cases=256
    for case in range(cases):
        vals={n:rng.randrange(1,7) if case < cases//2 else rng.randrange(-6,7) for n in z}
        env=execute(source,vals); fac=factors(vals); result=prod(fac.values())-1
        assert all(env[n]==v for n,v in fac.items())
        assert env[out] == result and execute(ss,vals)[so] == result*result
    bounds=0
    for x in list(range(1,257))+[2**32+1,2**127+91]:
        r=48*x+15; X=2**31*(x+1); Y=1
        assert r>=63 and X>4*r+6 and X*Y>2*(2*r+3)
        assert r.bit_count()==(3*x).bit_count()+4>=5
        for eps in (-1,1):
            for lam in (-1,1):
                assert 0<2*(r+eps)-lam<X*Y
                k=X*Y+r+eps; c=k*Y+1
                assert c>k>X*Y>2*(2*r+3)
        bounds+=1
    signs=0
    for g in range(4):
      for D in (0,3):
       for v in range(4):
        for y in range(4):
         for t in range(4):
          assert (g*g)%4 != 3
          assert (v*v-D*y*y)%4 != 3
          assert ((D*t)**2*(v*v-y*y)+y*y)%4 != 3
          signs+=1
    recurrences=0
    for X in (8,16,64,128):
      for Y in (1,2,16,32,80):
       a=Y*(X+1); A=a+2; H=4*a+3; E=X*Y; P=2*X*Y*Y+1
       for n in range(1,33):
        ch,ps=pell(A,n,H); assert (ch-a*ps)%H==pow(2,n,H)
        assert pell(P,n,E)[1]==n%E
        recurrences+=1
    aux=[canonical_auxiliary(A,3) for A in range(3,9)]
    main=[canonical_main(1)]
    rows=json.loads(json.dumps(source))
    return dict(status='PASS_PELL_FIXED_AFFINE_EXPONENT',ledger=ledger(packet),sos_ledger=ledger(packet,sum_of_squares=True),
        parameters=PARAMETERS,auxiliaries=AUXILIARIES,interfaces=packet['interfaces'],source=rows,output=out,
        source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),
        exact_factor_degrees=exact_degrees,symbolic_factor_identities=6,main_cancellation_identity=True,
        assignments=cases,signed=cases//2,complete_outputs=2*cases,
        sign_residues=signs,pretyping_bound_cases=bounds,modular_recurrences=recurrences,
        canonical_main=main,canonical_auxiliary=aux,
        theorem='For every positive x, the positive zero set projects exactly to computed Q=8^(32*x).',
        scope='Standalone exponent component, not a universal compiler or a numerical full huge Pell witness.')


if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--write',action='store_true'); args=parser.parse_args()
    result=json.loads(json.dumps(verify())); path=Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result,indent=2)+'\n')
    else: assert json.loads(path.read_text())==result, 'receipt mismatch'
    print(result['status']); print(result['ledger'])
