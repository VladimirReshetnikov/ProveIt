#!/usr/bin/env python3
"""Independent literal-formula, fixed-byte, DAG and exact-degree auditor.

This program imports neither build.py nor circuit.py. Finite evaluations audit
the emitted implementation; the included proofs establish the unbounded theorem.
Polynomial identities and diagonal leading coefficients below are exact checks.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
from itertools import product
import gzip
import json

ROOT = Path(__file__).resolve().parent
PRIMES = (101, 1009, 1000003)


def check(value, label):
    if not value:
        raise ValueError(label)


def read_json(path):
    return json.loads((ROOT / path).read_text())


def fixed_values():
    binding = read_json('coefficients/COEFFICIENT_BINDING.json')
    native = {}
    for r in binding['materialization']['files']:
        packed = (ROOT / 'coefficients' / r['file']).read_bytes()
        raw = gzip.decompress(packed)
        check(sha256(packed).hexdigest() == r['gzip_sha256'], 'native packed hash')
        check(sha256(raw).hexdigest() == r['sha256'], 'native full integer hash')
        native[r['port']] = int.from_bytes(raw, 'little')
    ports = [native[n] for n in ('beta','K','MC','MF_source')]
    values = {}
    manifest = read_json('fixed/FIXED_BINDING.json')
    for r in manifest['files']:
        packed = (ROOT / 'fixed' / r['file']).read_bytes()
        raw = gzip.decompress(packed)
        check(sha256(packed).hexdigest() == r['gzip_sha256'], 'fixed packed hash')
        check(sha256(raw).hexdigest() == r['sha256'], 'fixed full integer hash')
        value = r['sign'] * int.from_bytes(raw, 'little')
        check(abs(value).bit_length() == r['bits'], 'fixed bit length')
        if 'recipe' in r:
            expected = 0
            for term in r['recipe']:
                v = term['coefficient']
                for port, exponent in zip(ports, term['powers']):
                    v *= port ** exponent
                expected += v
        else:
            expected = 2 ** r['power_of_two_exponent']
        check(value == expected, 'fixed recipe value')
        values[r['name']] = value
    return values, ports


def structure(body, fixed):
    nodes = body['nodes']
    counts = Counter()
    names = []
    for i, n in enumerate(nodes):
        k = n['kind']
        check(k in ('variable','literal','fixed','add','sub','mul'), 'known node type')
        if k in ('add','sub','mul'):
            check(0 <= n['left'] < i and 0 <= n['right'] < i, 'DAG order')
            counts[k] += 1
        elif k == 'variable':
            names.append(n['name'])
        elif k == 'fixed':
            check(n['name'] in fixed, 'fixed leaf bound')
    check(set(names) == set(body['variables']), 'exact variable list')
    check(len(names) == len(set(names)), 'unique variable leaves')
    check(dict(counts) == body['operation_counts'], 'operation breakdown')
    check(sum(counts.values()) == body['total_operations'], 'operation total')
    live, todo = set(), [body['output']]
    while todo:
        i = todo.pop()
        if i in live:
            continue
        check(0 <= i < len(nodes), 'node reference')
        live.add(i)
        n = nodes[i]
        if n['kind'] in ('add','sub','mul'):
            todo.extend((n['left'], n['right']))
    check(len(live) == len(nodes), 'no dead gates')
    return sum(counts.values())


def evaluate(body, fixed, variables, p):
    values = []
    for n in body['nodes']:
        k = n['kind']
        if k == 'variable':
            v = variables[n['name']]
        elif k == 'literal':
            v = n['value']
        elif k == 'fixed':
            v = fixed[n['name']]
        else:
            a, b = values[n['left']], values[n['right']]
            v = a+b if k == 'add' else a-b if k == 'sub' else a*b
        values.append(v % p)
    return values[body['output']], {n: values[i] for n,i in body['named_nodes'].items()}


def literal_source(b, g, ports, p):
    data = read_json('data/degree_channels.json')
    cert = data['certificate']
    B = pow(2,1182968,p)*b*b % p
    channels = []
    for d in (0,1,2):
        total = 0
        for row in data['channels'][str(d)]:
            co = 0
            for t in row['recipe']:
                v = t['coefficient']
                for port, exponent in zip(ports, t['powers']):
                    v = v*pow(port % p,exponent,p) % p
                co += v
            total += co*pow(B,row['exponent'],p)
        channels.append(total % p)
    ell = sum(pow(B,e,p) for e in cert['weights']) % p
    At = sum(pow(B,e,p) for e in cert['targets']) % p
    y = (g+ell) % p
    F = (channels[2]*y*y+channels[1]*y+channels[0]+pow(B,1915,p)*(y*y+1)) % p
    N0 = pow(B,109,p)
    mask = (N0-1-(b-1)*ell) % p
    Sc = (g+N0*(2*F+At)) % p
    Tc = (mask+N0*(B-2)*At) % p
    return B,Sc,Tc


def literal_nine(v, positive, ports, p):
    if positive:
        b=v['epsilon_plus']+1
        g,h,s,w,i=(v[n] for n in ('g','h','s','w','i'))
        phi,j,n=(v[n+'_plus']-1 for n in ('phi','j','n'))
    else:
        b=v['epsilon']+2
        g,h,s,w,i=(v[n+'0']+1 for n in ('g','h','s','w','i'))
        phi,j,n=(v[n] for n in ('phi','j','n'))
    B,Sc,Tc=literal_source(b,g,ports,p)
    mod=lambda x:x%p
    L=mod(4*b*pow(B,2241,p))
    R=mod((Sc+Tc)*L+L-1-Sc)
    N=mod(pow(2,9463734,p)*b*pow(B,1178,p))
    cap=mod(32*b*pow(B,108,p))
    U,Y=mod(N*N*w),mod(N*N*s)
    M0=mod(R*Y)
    P=mod(2*M0*M0*U)
    K=mod(R+1+h*(P-1))
    A=mod(M0*(U+1))
    B1,W1=mod(2*R+1),mod(b*w)
    C=mod(B1+W1+phi)
    J=mod(4*A-5)
    Q=mod(3*W1*C-2*(W1*W1-1))
    D=mod((A*A-1)*C*C+1)
    E=mod(i*J*D*C*C)
    F=mod((A*A-1)*E*E+1)
    G=mod(A+F*(C*D+1-A))
    H=mod(C+F*(B1+j*C))
    I=mod((G*G-1)*H*H+1)
    a0=mod((P*P-1)*K*K+1)
    a1=mod(64*D*F*I)
    mu=mod((K*K-4*(C-K*Y)**2)*cap-8*g*K*K)
    V0=mod(P*K)
    t0=mod(i*J*C)
    T0=mod(t0*(8*D*D-4*D-1))
    V1=mod(T0*G*H)
    Om=mod(J*mu)
    theta=mod(J*n+Q-Om*(V0+V1))
    result=mod((theta*theta-Om*Om*(a0+a1))**2-4*Om**4*a0*a1)
    registers=dict(R=R,N=N,Scode=Sc,Tcode=Tc,P=P,K=K,A=A,C=C,J=J,Q=Q,
                   D=D,E=E,F=F,G=G,H=H,I=I,mu=mu,V0=V0,V1=V1,F9=result)
    return result,registers


def literal_ten(v, ports, p):
    f,g,h,k,l,w,x,y,z,m=(v[n] for n in ('f','g','h','k','l','w','x','y','z','m'))
    mod=lambda a:a%p
    b=1+3*f
    B,Sc,Tc=literal_source(b,g,ports,p)
    Lc=pow(B,2241,p)
    X=mod(Lc*Lc+(Sc+Tc)*Lc+Lc-1-Sc)
    Y=mod(pow(2,1182968*16-21,p)*pow(B,2356,p)*b)
    cap=mod(b*pow(B,108,p))
    L=mod(l*Y)
    U,V,W=mod(2*L*X),mod(4*g*w*Y),mod(b*w)
    A=mod(U*(V+1))
    B1=mod(2*X+1)
    C=mod(B1+(A-2)*h)
    P=mod(U*U*V)
    K=mod(X+1+k*(P-2))
    S=mod(2*A-5)
    T=mod(3*W*C-2*(W*W-1))
    R2=mod((P*P-4)*K*K+4)
    delta=mod(8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K))
    O=mod(f*f*l*l*delta)
    xi=mod(z*x)
    D=mod((A*A-4)*C*C+4)
    E=mod(C*C*D*xi)
    F=mod(4*(A*A-4)*E*E+1)
    G=mod(2*(A+2)*(A-2)**2*E*E-1)
    H=mod(C+(B1-C)*F+16*E*F*y)
    I=mod((G*G-1)*H*H+1)
    sig=mod(xi*S**5)
    r=mod(T+S*y)
    theta=mod((r**3-r*S*S-S**3)*(r*r+23*S*S))
    a0=mod(b*(1+(3*O-4)*b*b*z*z))
    a1,a2=R2,mod(D*F*I)
    w1=a0
    w2=mod(a0*(P*P+K*K+3))
    Z=mod(sig*m-theta)
    q0,q1,q2=mod(sig*sig*a0),mod(sig*sig*w1*w1*a1),mod(sig*sig*w2*w2*a2)
    Vn=mod(Z*Z+q2-q0-q1)
    Wn=mod(Vn*Vn+4*Z*Z*q2-4*q0*q1)
    result=mod(Wn*Wn-16*Vn*Vn*Z*Z*q2)
    registers=dict(X=X,Y=Y,Scode=Sc,Tcode=Tc,A=A,C=C,Pn=P,K=K,
                   D=D,E=E,F=F,Gstar=G,Hstar=H,Istar=I,F10=result)
    return result,registers


def leading_certificate(body, fixed, p):
    rows=[]
    for n in body['nodes']:
        k=n['kind']
        if k=='variable':
            row=(1,1)
        elif k in ('literal','fixed'):
            row=(0,(n['value'] if k=='literal' else fixed[n['name']])%p)
        else:
            da,a=rows[n['left']]
            db,b=rows[n['right']]
            if k=='mul':
                row=(da+db,a*b%p)
            else:
                sign=1 if k=='add' else -1
                row=(max(da,db),((a if da>=db else 0)+sign*(b if db>=da else 0))%p)
        rows.append(row)
    return rows[body['output']]


class Poly:
    """Tiny exact sparse Z-polynomial ring, independent of every DAG builder."""
    size=8
    def __init__(self, terms):
        self.terms={e:c for e,c in terms.items() if c}
    @staticmethod
    def const(x):
        return Poly({(0,)*Poly.size:x})
    @staticmethod
    def var(i):
        e=[0]*Poly.size
        e[i]=1
        return Poly({tuple(e):1})
    def __add__(self,other):
        if not isinstance(other,Poly): other=Poly.const(other)
        d=self.terms.copy()
        for e,c in other.terms.items():d[e]=d.get(e,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({e:-c for e,c in self.terms.items()})
    def __sub__(self,other):return self+-other if isinstance(other,Poly) else self+(-other)
    def __rsub__(self,other):return -self+other
    def __mul__(self,other):
        if not isinstance(other,Poly):other=Poly.const(other)
        d={}
        for e,c in self.terms.items():
            for f,b in other.terms.items():
                ef=tuple(x+y for x,y in zip(e,f))
                d[ef]=d.get(ef,0)+c*b
        return Poly(d)
    __rmul__=__mul__
    def __pow__(self,n):
        ans=Poly.const(1)
        for _ in range(n):ans=ans*self
        return ans


def identities():
    D,t,G,H,E0,Om,V0,K=(Poly.var(i) for i in range(8))
    F=(D-1)*t*t*D*D+1
    T=t*(8*D*D-4*D-1)
    err=t*t*(8*D+1)-64*D
    check(not (T*T-64*D*F-err).terms,'second-order Pell majorant identity')
    I=(G*G-1)*H*H+1
    V1=T*G*H
    a1=64*D*F*I
    defect=err*G*G*H*H+64*D*F*(H*H-1)
    check(not (V1*V1-a1-defect).terms,'majorant defect identity')
    # Independent cancellation identity, with delta as a free indeterminate.
    e,o,v0,v1,kk,delta=(Poly.var(i) for i in range(6))
    aa0=v0*v0-kk*kk+1
    aa1=v1*v1-delta
    original=(e-o*(v0+v1))**2-o*o*(aa0+aa1)
    reduced=e*e-2*e*o*(v0+v1)+o*o*(kk*kk-1+delta+2*v0*v1)
    check(not (original-reduced).terms,'exact nine degree cancellation')
    z,r0,r1,r2=(Poly.var(i) for i in range(4))
    vv=z*z+r2*r2-r0*r0-r1*r1
    ww=vv*vv+4*z*z*r2*r2-4*r0*r0*r1*r1
    norm=ww*ww-16*vv*vv*z*z*r2*r2
    factored=Poly.const(1)
    for s0,s1,s2 in product((-1,1),repeat=3):
        factored=factored*(z+s0*r0+s1*r1+s2*r2)
    check(not (norm-factored).terms,'eight-factor norm identity')
    return dict(exact_polynomial_identities=4,three_radical_norm_terms=len(norm.terms))


def main():
    fixed,ports=fixed_values()
    out=dict(status='PASS',scope='Exact finite implementation and coefficient audit; see report for unbounded proofs.',
             fixed_leaves_checked=len(fixed),identities=identities(),equations={})
    for label,count,expected_degree in [('nine_positive',9,2628944),('nine_natural',9,2628944),('ten_integer',10,8317400)]:
        body=read_json('generated/'+label+'.json')
        ops=structure(body,fixed)
        check(len(body['variables'])==count,'advertised number of unknowns')
        cert=(read_json('generated/'+label+'_degree_certificate.json') if count==9 else body)
        structure(cert,fixed)
        tests=0
        heads={}
        for p in PRIMES:
            for case in range(24):
                v={name:((case+1)*(i+3)+(case*i*i))%p for i,name in enumerate(body['variables'])}
                actual,regs=evaluate(body,fixed,v,p)
                expected,reference=(literal_nine(v,label=='nine_positive',ports,p) if count==9 else literal_ten(v,ports,p))
                check(actual==expected,'literal full equation modulo prime')
                for name,value in reference.items():
                    check(regs[name]==value,'literal named register '+name)
                check(evaluate(cert,fixed,v,p)[0]==actual,'degree circuit represents same equation')
                tests+=1
            degree,head=leading_certificate(cert,fixed,p)
            check(degree==expected_degree,'multivariate upper degree')
            heads[str(p)]=head
        check(any(heads.values()),'nonzero exact top diagonal coefficient')
        out['equations'][label]=dict(unknowns=count,operations=ops,exact_degree=expected_degree,
                                    exact_leading_residues=heads,literal_modular_assignments=tests)
    (ROOT/'certificates/INDEPENDENT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
