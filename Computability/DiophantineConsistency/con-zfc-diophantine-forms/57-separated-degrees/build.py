#!/usr/bin/env python3
"""Explicit degree-channel consistency polynomials; Python standard library.

All powers are fixed. Circuits are division-free. Numerical constants are
bound to one authenticated native tuple; no consistency-dependent choice occurs.
See NOTICE.md for the inherited Jones/Sun circuits and coefficient compiler.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import json
from hashlib import sha256
from circuit import DAG

ROOT = Path(__file__).resolve().parent
PORT_BITS = [590069, 592884, 590069, 590070]
KAPPA = 1182968
DATA = json.loads((ROOT / 'data/degree_channels.json').read_text())
CERT = DATA['certificate']
W, QC = CERT['W'], CERT['Q']
KC, EC, HC = QC + 2*W + 1, QC + 3*W + 3, QC + 4*W + 26


def require(test, message):
    if not test:
        raise ValueError(message)


class Source:
    def __init__(self, dag, b, g, mode='horner'):
        self.d = d = dag
        A, M, S, P, c = d.plus, d.times, d.minus, d.power, d.const
        self.B = B = d.save('Bcode', M(d.fixed('base_scale'), P(b, 2)))

        @lru_cache(None)
        def chunk(pos, digit):
            if digit == 0:
                return c(1)
            if digit == 1:
                return B if pos == 0 else P(chunk(pos-1, 1), 16)
            return M(chunk(pos, digit-1), chunk(pos, 1))

        @lru_cache(None)
        def bp(n):
            require(n >= 0, 'negative exponent')
            if mode == 'binary':
                return P(B, n)
            out, pos = [], 0
            while n:
                if n % 16:
                    out.append(chunk(pos, n % 16))
                n //= 16
                pos += 1
            return M(*out)

        self.bp = bp
        self.recipes = []
        self.bound = 0
        recipe_ids = {}

        def coefficient(recipe):
            key = tuple((tuple(t['powers']), t['coefficient']) for t in recipe)
            bound = sum(abs(co) * (1 << sum(a*b for a,b in zip(ex, PORT_BITS)))
                        for ex,co in key)
            self.bound = max(self.bound, bound)
            if len(key) == 1 and not any(key[0][0]):
                return c(key[0][1])
            if key not in recipe_ids:
                name = 'coefficient_%02d' % len(recipe_ids)
                recipe_ids[key] = name
                self.recipes.append(dict(name=name, terms=recipe))
            return d.fixed(recipe_ids[key])

        def polynomial(terms):
            terms = sorted(terms, reverse=True)
            if not terms:
                return c(0)
            if mode == 'direct':
                return A(*(M(value, bp(ex)) for ex, value in terms))
            prev, out = terms[0]
            for ex, value in terms[1:]:
                out = A(M(out, bp(prev-ex)), value)
                prev = ex
            return M(out, bp(prev))

        channel = {}
        for degree in (0, 1, 2):
            terms = [(r['exponent'], coefficient(r['recipe']))
                     for r in DATA['channels'][str(degree)]]
            channel[degree] = d.save('channel_%d' % degree, polynomial(terms))
        self.ell = ell = d.save('ell', A(*(bp(i) for i in CERT['weights'])))
        targets = d.save('targets', polynomial([(q, c(1)) for q in CERT['targets']]))
        packed = d.save('packed_positive', A(g, ell))
        packed2 = P(packed, 2)
        carrier = bp(QC+1)
        source = d.save('source_value', A(M(A(channel[2], carrier), packed2),
                                        M(channel[1], packed), channel[0], carrier))
        self.N0 = N0 = d.save('N0', bp(W+1))
        mask = d.save('low_mask', S(S(N0, c(1)), M(S(b, c(1)), ell)))
        jcode = d.save('Jcode', A(M(c(2), source), targets))
        self.S = d.save('Scode', A(g, M(N0, jcode)))
        self.T = d.save('Tcode', A(mask, M(N0, S(B, c(2)), targets)))
        require(self.bound.bit_length() == 1182955, 'coefficient bound changed')
        require(KAPPA % 2 == 0 and KAPPA >= self.bound.bit_length()+13,
                'base majorant too small')


def finish(d, root, variables, name, source, **extra):
    nodes, output, named = d.prune(root)
    counts = dict(Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul')))
    return dict(schema='proveit-degree-channels-v1', name=name, variables=variables,
                nodes=nodes, output=output, named_nodes=named,
                operation_counts=counts, total_operations=sum(counts.values()),
                coefficient_recipes=source.recipes, base_scale_exponent=KAPPA,
                port_bits=PORT_BITS, source_coefficient_bound_exponent=1182955,
                W=W, Qcode=QC, Kcode=KC, Ecode=EC, Hpop=HC,
                native_binding='../coefficients/COEFFICIENT_BINDING.json', **extra)


def nine(positive=True, certificate=False, mode='horner', crt=True):
    d = DAG()
    A, M, S, P, c, save = d.plus, d.times, d.minus, d.power, d.const, d.save
    variables = (['epsilon_plus','g','h','s','w','phi_plus','i','j_plus','n_plus']
                 if positive else ['epsilon','g0','h0','s0','w0','phi','i0','j','n'])
    vv = {n:d.var(n) for n in variables}
    if positive:
        v = {n:vv[n] for n in ('g','h','s','w','i')}
        v.update({n:S(vv[n+'_plus'], c(1)) for n in ('epsilon','phi','j','n')})
        b = save('b', A(vv['epsilon_plus'], c(1)))
    else:
        v = {n:A(vv[n+'0'], c(1)) for n in ('g','h','s','w','i')}
        v.update({n:vv[n] for n in ('epsilon','phi','j','n')})
        b = save('b', A(v['epsilon'], c(2)))
    src = Source(d, b, v['g'], mode)
    bp = src.bp
    L = save('Lcode', M(c(4), b, bp(EC)))
    R = save('R', A(M(A(src.S, src.T), L), S(S(L, c(1)), src.S)))
    if HC % 2:
        threshold_exponent = 15*KAPPA//2-10
        N = save('N', M(d.fixed('threshold_scale'), bp((HC-15)//2)))
    else:
        threshold_exponent = 8*KAPPA-10
        N = save('N', M(d.fixed('threshold_scale'), b, bp((HC-16)//2)))
    Gcap = save('Gcap', M(c(32), b, bp(W)))
    N2 = P(N,2)
    U = save('U', M(N2,v['w']))
    Y = save('Y', M(N2,v['s']))
    M0 = save('M0', M(R,Y))
    PP = save('P', M(c(2),P(M0,2),U))
    K = save('K', A(R,c(1),M(v['h'],S(PP,c(1)))))
    AA = save('A', M(M0,A(U,c(1))))
    B1 = save('B1', A(M(c(2),R),c(1)))
    W1 = save('W1', M(b,v['w']))
    C = save('C', A(B1,W1,v['phi']))
    J = save('J', S(M(c(4),AA),c(5)))
    Q = save('Q', S(M(c(3),W1,C),M(c(2),S(P(W1,2),c(1)))))
    Am1 = S(P(AA,2),c(1))
    D = save('D', A(M(Am1,P(C,2)),c(1)))
    E = save('E', M(v['i'],J,D,P(C,2)))
    F = save('F', A(M(Am1,P(E,2)),c(1)))
    G = save('G', A(AA,M(F,S(A(M(C,D),c(1)),AA))))
    if crt:
        H = save('H', A(C,M(F,A(B1,M(v['j'],C)))))
        u, vc = save('u',J), save('v',Q)
    else:
        H = save('H', A(B1,M(A(v['j'],c(1)),C)))
        u, vc = save('u',M(J,F)), save('v',A(M(Q,F),M(J,S(H,C))))
    I = save('I', A(M(S(P(G,2),c(1)),P(H,2)),c(1)))
    V0 = save('V0', M(PP,K))
    a0 = save('a0', A(S(P(V0,2),P(K,2)),c(1)))
    a1 = save('a1', M(c(64),D,F,I))
    mu = save('mu', S(M(S(P(K,2),M(c(4),P(S(C,M(K,Y)),2))),Gcap),
                       M(c(8),v['g'],P(K,2))))
    t0 = save('t0', M(v['i'],J,C))
    T0 = save('T0', M(t0,S(S(M(c(8),P(D,2)),M(c(4),D)),c(1))))
    GH = save('GH', M(G,H))
    V1 = save('V1', M(T0,GH))
    vsum = save('Vsum', A(V0,V1))
    Om = save('Omega', M(u,mu))
    e0 = save('E0', A(M(u,v['n']),vc))
    theta = save('Theta', S(e0,M(Om,vsum)))
    if certificate:
        error = save('DF_error', S(M(P(t0,2),A(M(c(8),D),c(1))),M(c(64),D)))
        delta = save('delta1', A(M(error,P(GH,2)),M(c(64),D,F,S(P(H,2),c(1)))))
        inner = save('inner', A(S(P(e0,2),M(c(2),e0,Om,vsum)),
                               M(P(Om,2),A(S(P(K,2),c(1)),delta,M(c(2),V0,V1)))))
    else:
        inner = save('inner', S(P(theta,2),M(P(Om,2),A(a0,a1))))
    out = save('F9', S(P(inner,2),M(c(4),P(Om,4),a0,a1)))
    return finish(d,out,variables,'nine_'+('positive' if positive else 'natural'),src,
                  domain='positive integers' if positive else 'nonnegative integers',
                  threshold_scale_exponent=threshold_exponent, encoding=mode,
                  crt_reparameterized=crt, degree_certificate_variant=certificate)


def norm3(d, center, a0, a1, a2):
    A,M,S,P,c = d.plus,d.times,d.minus,d.power,d.const
    x2=P(center,2)
    v=S(S(A(x2,a2),a0),a1)
    v2=P(v,2)
    t=M(c(4),x2,a2)
    q=S(A(v2,t),M(c(4),a0,a1))
    return S(P(q,2),M(c(4),v2,t))


def ten(mode='horner'):
    d=DAG()
    A,M,S,P,c,save=d.plus,d.times,d.minus,d.power,d.const,d.save
    variables=['f','g','h','k','l','w','x','y','z','m']
    v={n:d.var(n) for n in variables}
    b=save('b',A(c(1),M(c(3),v['f'])))
    src=Source(d,b,v['g'],mode)
    bp=src.bp
    Lcode=save('Lcode',bp(EC))
    X=save('X',A(P(Lcode,2),M(A(src.S,src.T),Lcode),S(S(Lcode,c(1)),src.S)))
    Y=save('Y',M(P(d.fixed('base_scale'),15),d.fixed('mask_scale'),bp(HC-16),b))
    cap=save('Ccap',M(b,bp(W)))
    L=save('Lsmall',M(v['l'],Y))
    U=save('U',M(c(2),L,X))
    V=save('V',M(c(4),v['g'],v['w'],Y))
    Wsmall=save('Wsmall',M(b,v['w']))
    AA=save('A',M(U,A(V,c(1))))
    BB=save('Bsmall',A(M(c(2),X),c(1)))
    C=save('C',A(BB,M(S(AA,c(2)),v['h'])))
    PP=save('Pn',M(P(U,2),V))
    K=save('K',A(X,c(1),M(v['k'],S(PP,c(2)))))
    SS=save('Ssmall',S(M(c(2),AA),c(5)))
    TT=save('Tsmall',S(M(c(3),Wsmall,C),M(c(2),S(P(Wsmall,2),c(1)))))
    R2=save('R2',A(M(S(P(PP,2),c(4)),P(K,2)),c(4)))
    cap3=P(cap,3)
    delta=save('Delta',S(M(c(8),cap3,v['g'],P(K,2)),
                         M(P(v['g'],2),A(M(c(32),P(S(C,M(K,L)),2),cap3),
                                            M(P(v['g'],2),P(K,2))))))
    O0=save('O0',M(P(v['f'],2),P(v['l'],2),delta))
    xi=save('xi',M(v['z'],v['x']))
    D=save('D',A(M(S(P(AA,2),c(4)),P(C,2)),c(4)))
    E=save('E',M(P(C,2),D,xi))
    F=save('F',A(M(c(4),S(P(AA,2),c(4)),P(E,2)),c(1)))
    GG=save('Gstar',S(M(c(2),A(AA,c(2)),P(S(AA,c(2)),2),P(E,2)),c(1)))
    Om=save('Omega',M(c(16),E))
    HH=save('Hstar',A(C,M(S(BB,C),F),M(Om,F,v['y'])))
    II=save('Istar',A(M(S(P(GG,2),c(1)),P(HH,2)),c(1)))
    sigma=save('Sigma',M(xi,P(SS,5)))
    rr=save('merger_argument',A(TT,M(SS,v['y'])))
    ss2=P(SS,2)
    theta=save('Theta',M(S(S(P(rr,3),M(rr,ss2)),M(ss2,SS)),A(P(rr,2),M(c(23),ss2))))
    bracket=save('positivity_bracket',A(c(1),M(S(M(c(3),O0),c(4)),P(b,2),P(v['z'],2))))
    aa0=save('A1',M(b,bracket))
    aa1=save('A2',R2)
    aa2=save('A3',M(D,F,II))
    weight1=save('norm_weight1',aa0)
    weight2=save('norm_weight2',M(weight1,A(P(PP,2),P(K,2),c(3))))
    center=save('norm_center',S(M(sigma,v['m']),theta))
    s2=P(sigma,2)
    b0=save('scaled_A1',M(s2,aa0))
    b1=save('scaled_A2',M(s2,P(weight1,2),aa1))
    b2=save('scaled_A3',M(s2,P(weight2,2),aa2))
    out=save('F10',norm3(d,center,b0,b1,b2))
    return finish(d,out,variables,'ten_integer',src,domain='unrestricted integers',
                  mask_scale_exponent=KAPPA-21, encoding=mode)


def degree_certificate(body):
    """Degree upper bounds plus exact diagonal leaders in fixed symbols a,c.

    Cancellation-resolved circuits are used for nine variables. Unknown
    coefficient heads are kept unknown, never assumed nonzero. A positive
    final leader establishes the exact multivariate total degree.
    """
    rows=[]
    unresolved=[]
    for idx,node in enumerate(body['nodes']):
        kind=node['kind']
        if kind=='variable':
            row=(1,{(0,0,0):1})
        elif kind=='literal':
            row=(0,{(0,0,0):node['value']})
        elif kind=='fixed':
            keys={'base_scale':(1,0,0),'threshold_scale':(0,1,0),'mask_scale':(0,0,1)}
            row=(0,{keys[node['name']]:1} if node['name'] in keys else None)
        else:
            da,ca=rows[node['left']]
            db,cb=rows[node['right']]
            if kind=='mul':
                if ca is None or cb is None:
                    row=(da+db,None)
                else:
                    cc={}
                    for ex,x in ca.items():
                        for ey,y in cb.items():
                            ez=tuple(a+b for a,b in zip(ex,ey))
                            cc[ez]=cc.get(ez,0)+x*y
                    row=(da+db,{ex:x for ex,x in cc.items() if x})
            else:
                sign=1 if kind=='add' else -1
                if da>db:
                    row=(da,ca)
                elif db>da:
                    row=(db,None if cb is None else {ex:sign*x for ex,x in cb.items()})
                elif ca is None or cb is None:
                    row=(da,None)
                else:
                    cc=ca.copy()
                    for ex,x in cb.items():
                        cc[ex]=cc.get(ex,0)+sign*x
                    cc={ex:x for ex,x in cc.items() if x}
                    if not cc and da>0:
                        unresolved.append(idx)
                    row=(da,cc)
        rows.append(row)
    deg,leader=rows[body['output']]
    require(leader is not None and bool(leader), 'unknown final leader')
    require(not unresolved, 'unresolved leading cancellation: '+str(unresolved))
    # The actual fixed scales are powers of two. Symbolic terms are evaluated
    # as exponents, avoiding construction of billion-bit final coefficients.
    exponents=[]
    for ex,x in leader.items():
        require(x>0, 'leader requires a sign audit')
        twos=(x & -x).bit_length()-1
        odd=x >> twos
        odd_record=(str(odd) if odd.bit_length()<512 else
                    dict(positive=True,bit_length=odd.bit_length(),
                         sha256_unsigned_little_endian=sha256(odd.to_bytes((odd.bit_length()+7)//8,'little')).hexdigest()))
        exponents.append(dict(base_scale_power=ex[0],threshold_scale_power=ex[1],
                              mask_scale_power=ex[2],scalar_power_of_two=twos,
                              scalar_odd_part=odd_record))
    return dict(exact_degree=deg,diagonal_leading_coefficient=exponents,
                named_degrees={n:rows[i][0] for n,i in body['named_nodes'].items()},
                method='Multivariate upper bounds attained by a positive exact diagonal leading coefficient.')


def main():
    out=ROOT/'generated'
    out.mkdir(exist_ok=True)
    ledger={}
    for positive in (True,False):
        label='nine_'+('positive' if positive else 'natural')
        variants=[nine(positive,False,mode,crt) for mode in ('horner','direct','binary') for crt in (True,False)]
        best=min(variants,key=lambda x:x['total_operations'])
        certificate=nine(positive,True,best['encoding'],best['crt_reparameterized'])
        degree=degree_certificate(certificate)
        for suffix,body in [('',best),('_degree_certificate',certificate)]:
            body['exact_degree']=degree['exact_degree']
            (out/(label+suffix+'.json')).write_text(json.dumps(body,separators=(',',':'))+'\n')
        (out/(label+'_degree.json')).write_text(json.dumps(degree,indent=2)+'\n')
        ledger[label]=dict(degree=degree['exact_degree'],operations=best['total_operations'],
                           operation_counts=best['operation_counts'],encoding=best['encoding'],
                           crt=best['crt_reparameterized'])
    variants=[ten(mode) for mode in ('horner','direct','binary')]
    best=min(variants,key=lambda x:x['total_operations'])
    degree=degree_certificate(best)
    best['exact_degree']=degree['exact_degree']
    (out/'ten_integer.json').write_text(json.dumps(best,separators=(',',':'))+'\n')
    (out/'ten_integer_degree.json').write_text(json.dumps(degree,indent=2)+'\n')
    ledger['ten_integer']=dict(degree=degree['exact_degree'],operations=best['total_operations'],
                              operation_counts=best['operation_counts'],encoding=best['encoding'])
    (out/'METRICS.json').write_text(json.dumps(ledger,indent=2)+'\n')
    print(json.dumps(ledger,indent=2))


if __name__=='__main__':
    main()
