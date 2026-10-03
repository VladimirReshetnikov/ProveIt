"""Exact Q=8**(32*x) with a 52-operation positive exponent component.

The literal 53-operation parent is guarded in full. The changed Pell
indices require fresh witnesses; no same-tuple or off-zero identity with
that parent is asserted. Both signs of the complete unit product have
an exact necessary power projection.
"""
import argparse
from collections import Counter
import hashlib
import json
from math import comb, prod
from pathlib import Path
import random

import pell_fixed_affine_exponent as parent

PARAMETERS = list(parent.PARAMETERS)
AUXILIARIES = list(parent.AUXILIARIES)
FACTOR_NAMES = list(parent.FACTOR_NAMES)
execute = parent.execute
pell = parent.pell


def rewrite(old):
    assert old == parent.build(), 'complete canonical53 parent required'
    expected = {'r_scaled': ('*',48,'x'), 'r': ('+','r_scaled',15),
                'Q': ('+','x','delta'), 'X': ('*',2**31,'Q'),
                'V': ('-','of','c'), 'linear_gap': ('-','V','jc')}
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert all(rows[n]==row for n,row in expected.items())
    assert {n for n,_,a,b in old['source'] if 'r_scaled' in (a,b)} == {'r'}
    change={'r_scaled':('r','*',48,'x'), 'Q':('Q','+','r','delta'),
            'X':('X','*',2,'Q'), 'V':('V','+','of','c'),
            'linear_gap':('linear_gap','-','jc','V')}
    source=[change.get(n,row) for row in old['source'] for n in [row[0]] if n!='r']
    result=dict(old,source=source,positive_plus_auxiliary=True,
                witness_equivalence='Same computed input/output relation with fresh positive witnesses; not a tuple bijection.')
    assert len(source)==len(old['source'])-1
    return result


def build(): return rewrite(parent.build())


def polynomial_source(packet=None, *, sum_of_squares=False):
    if packet is None: packet=build()
    assert packet==build(), 'literal canonical52 packet required'
    source=list(packet['source'])+[('output','-',packet['unit_register'],1)]
    output='output'
    if sum_of_squares: source.append(('output_square','*',output,output)); output='output_square'
    return source,output


def degrees(packet=None, *, sum_of_squares=False):
    if packet is None: packet=build()
    source,output=polynomial_source(packet,sum_of_squares=sum_of_squares)
    degrees={name:1 for name in PARAMETERS+AUXILIARIES}
    degree=lambda v: degrees[v] if isinstance(v,str) else 0
    for name,op,a,b in source:
        degrees[name]=degree(a)+degree(b) if op=='*' else max(degree(a),degree(b))
        if name=='N1':
            # Exact identity, independent of every norm equation.
            degrees[name]=max(2*degrees['L'],degrees['L']+degrees['a']+degrees['c'],
                              degrees['H']+2*degrees['c'])
    return degrees,degrees[output]


def ledger(packet=None, *, sum_of_squares=False):
    if packet is None: packet=build()
    source,_=polynomial_source(packet,sum_of_squares=sum_of_squares)
    count=Counter(op for _,op,_,_ in source); cert=Counter(op for _,op,_,_ in packet['source'])
    return dict(operations=len(source),multiplications=count['*'],
        additions_subtractions=count['+']+count['-'],certificate=len(packet['source']),
        certificate_multiplications=cert['*'],certificate_additions=cert['+']+cert['-'],
        equations=1,witnesses=len(AUXILIARIES),parameters=len(PARAMETERS),
        degree_bound=degrees(packet,sum_of_squares=sum_of_squares)[1])


def factors(z):
    r=48*z['x'];Q=r+z['delta'];X=2*Q;Y=z['s'];E=X*Y
    k=z['eta']+z['zeta'];c=k*Y+z['eta'];a=(X+1)*Y;H=4*a+3;Delta=(a+2)**2-1
    D=X+a*c+z['gamma']*H;t=z['i']*c*c;V=z['o']*z['f']+c;K=k-z['h']*E
    return dict(N0=z['g']**2+4*E*k*Y*(z['g']-k),N1=D*D-Delta*c*c,
                Ns=z['f']**2-Delta*t*t,N3=(Delta*t)**2*(V*V-z['y']**2)+z['y']**2,
                Nk=K-r,Nl=z['j']*c-V+2*K)


def canonical_main(x,epsilon=1):
    """Actual first/main coordinates; no gigantic auxiliary block is produced."""
    assert type(x) is int and x>=1 and type(epsilon) is int and epsilon in (-1,1)
    r=48*x;rr=r+epsilon-1;p=2*rr+1;X=2**p;Q=X//2
    Y=(X+1)**(2*rr)//X**rr;E=X*Y;a=(X+1)*Y;A=a+2;H=4*a+3
    D,c=pell(A,p);first,k=pell(2*X*Y*Y+1,rr+1)
    def div(u,v):
        q,rem=divmod(u,v);assert rem==0;return q
    z=dict(x=x,delta=Q-r,s=Y,eta=c-Y*k,zeta=(Y+1)*k-c,
           g=first-2*X*Y*Y*k,gamma=div(D-X-a*c,H),h=div(k-r-epsilon,E))
    assert min(z.values())>0 and Q==2**(96*x+(0 if epsilon==1 else -4))
    assert 0<c-Y*k<k and Y==sum(comb(2*rr,rr+j)*X**j for j in range(rr+1))
    assert z['g']**2+4*X*Y*Y*k*(z['g']-k)==1
    assert D*D-(A*A-1)*c*c==1 and k-z['h']*E-r==epsilon
    return dict(x=x,epsilon=epsilon,r=r,effective_r=rr,first_index=rr+1,main_index=p,
                positive_coordinates=True,first_main_index_equalities=True,
                Q_bits=Q.bit_length(),Y_bits=Y.bit_length(),c_bits=c.bit_length(),
                coordinate_bits={n:v.bit_length() for n,v in z.items()},
                scope='Actual first/main coordinates for the indicated signed branch, not a full large auxiliary zero.')


def canonical_auxiliary(A,p):
    assert type(A) is int and A>=2 and type(p) is int and p>=5 and p%4==1
    Delta=A*A-1;c=pell(A,p)[1];m=2*c*p;f,t=pell(A,m)
    i,rem=divmod(t,c*c);assert rem==0 and i>0
    T=Delta*t;chi,y=pell(T,p);V,rem=divmod(chi,T);assert rem==0
    o,rem=divmod(V-c,f);assert rem==0
    j,rem=divmod(V-p,c);assert rem==0
    assert min(f,i,j,o,y)>0 and V>T>f>c>p
    assert f*f-Delta*(i*c*c)**2==1
    assert T*T*(V*V-y*y)+y*y==1 and V==o*f+c==j*c+p
    return dict(A=A,p=p,m=m,positive_five_coordinates=True,three_auxiliary_equations=True,
                coordinate_bits={n:v.bit_length() for n,v in dict(f=f,i=i,j=j,o=o,y=y).items()},
                scope='Local plus-congruence auxiliary block; not a full x>=1 source zero.')


def guards():
    p=parent.build()
    bad=[dict(p,source=p['source'][:-1]),dict(p,interfaces={'nested':['r_scaled']}),
         dict(p,auxiliaries=p['auxiliaries'][:-1]),dict(p,unit_factors=p['unit_factors'][:-1]),
         dict(p,comparisons=[]),dict(p,parameters=['x','extra'])]
    for q in bad:
        try:rewrite(q)
        except AssertionError:pass
        else:raise AssertionError('noncanonical parent accepted')
    for key,value in [('interfaces',{'power':'x'}),('positive_plus_auxiliary',False),('unit_register','N0')]:
        q=dict(build());q[key]=value
        try:polynomial_source(q)
        except AssertionError:pass
        else:raise AssertionError('noncanonical successor accepted')
    return len(bad)+3


def verify():
    import sympy as sp
    packet=build();source,out=polynomial_source(packet);ss,so=polynomial_source(packet,sum_of_squares=True)
    for rows,target in ((source,out),(ss,so)):
        known=set(PARAMETERS+AUXILIARIES);parents={}
        for n,op,a,b in rows:
            assert n not in known and op in ('+','-','*')
            assert all(type(v) is int or v in known for v in (a,b))
            known.add(n);parents[n]=(a,b)
        seen=set();stack=[target]
        while stack:
            n=stack.pop()
            if isinstance(n,str) and n in parents and n not in seen:
                seen.add(n);stack.extend(parents[n])
        assert seen==set(parents)
        assert all(v in known for v in packet['interfaces'].values()) and 'r_scaled' not in known
    symbols={n:sp.Symbol(n) for n in PARAMETERS+AUXILIARIES}
    env=execute(packet['source'],symbols);manual=factors(symbols)
    fd={}
    for n in FACTOR_NAMES:
        assert sp.expand(env[n]-manual[n])==0
        fd[n]=sp.Poly(manual[n],*symbols.values()).total_degree()
    assert sp.expand(env['N1']-(env['L']**2+2*env['L']*env['a']*env['c']-env['H']*env['c']**2))==0
    assert fd==dict(zip(FACTOR_NAMES,(5,7,14,22,3,3)))
    assert sum(fd.values())==degrees(packet)[1]==54
    rng=random.Random(520491);cases=256
    for case in range(cases):
        vals={n:rng.randrange(1,8) if case<cases//2 else rng.randrange(-7,8) for n in symbols}
        ev=execute(source,vals);fac=factors(vals);U=prod(fac.values())-1
        assert all(ev[n]==v for n,v in fac.items())
        assert ev[out]==U and execute(ss,vals)[so]==U*U
    bounds=0
    for x in list(range(1,129))+[2**32+3,2**127+17]:
      for gap in (1,2,7):
       for Y in (1,2,3,16):
        r=48*x;X=2*(r+gap);E=X*Y;A=Y*(X+1)+2
        assert r>=48 and X>=2*r+2 and A>=2*r+5 and 2*A>4*r+6
        assert 2*X*Y*Y+1>A and 6*X*Y*Y>Y*(X+1)
        for eps in (-1,1):
            K=r+eps
            assert 0<K<E and K+E>=3*r+1>2*r+3
            for lam in (-1,1):assert 0<2*K-lam<=2*r+3<A
        bounds+=1
    small_signed=[]
    # Explicit pretyping corner where p<E is not an available argument.
    r=48;X=2*(r+1);E=X;K=r+1;candidate_p=2*K+1
    assert candidate_p>E and K+E>candidate_p
    for A in range(2,10):
      for p in (5,9,13,17):
       c=pell(A,p)[1];m=2*c*p
       # Check the canonical quotient polynomial congruences without
       # materializing f at the larger indices: evaluate L_p(1-A²) directly.
       def odd_quotient(z):
           a,b=1,4*z-3
           if p==1:return a
           for _ in range(1,(p-1)//2):a,b=b,(4*z-2)*b-a
           return b
       assert odd_quotient(1-A*A)==c and odd_quotient(0)==p
       small_signed.append([A,p])
    main=[canonical_main(1,e) for e in (1,-1)]
    aux=[canonical_auxiliary(A,5) for A in (2,3,4)]
    assert ledger()['operations']==52 and ledger()['multiplications']==31 and ledger()['additions_subtractions']==21
    rows=json.loads(json.dumps(source))
    return dict(status='PASS_PELL_FIXED_AFFINE_EXPONENT52',ledger=ledger(),sos_ledger=ledger(sum_of_squares=True),
        parameters=PARAMETERS,auxiliaries=AUXILIARIES,interfaces=packet['interfaces'],source=rows,output=out,
        source_sha256=hashlib.sha256(json.dumps(rows,separators=(',',':')).encode()).hexdigest(),
        exact_factor_degrees=fd,symbolic_factor_identities=6,main_cancellation_identity=True,
        assignments=cases,signed=cases//2,complete_outputs=2*cases,pretyping_bound_cases=bounds,
        no_p_less_E_corner=dict(r=r,E=E,p_candidate=candidate_p,first_wrapped_index=K+E),
        plus_quotient_identity_cases=small_signed,canonical_main=main,canonical_auxiliary=aux,
        rejected_mutations=guards(),
        theorem='Every positive x has a positive zero; computed Q=8^(32*x) at every positive zero.',
        signed_projection='If the six-factor product is epsilon in {-1,1}, Q=2^(96*x+2*epsilon-2).',
        scope='Paid exponent component with fresh witnesses; no universal compiler count or full giant Pell materialization.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['ledger'])
