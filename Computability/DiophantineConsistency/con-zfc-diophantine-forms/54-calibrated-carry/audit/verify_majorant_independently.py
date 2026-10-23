#!/usr/bin/env python3
"""Independent round-eight arithmetic audit. Imports no construction programs.

Checks finite polynomial identities, positivity certificates for all A>=729,
source-parametric defect dominance, source affine substitutions, factorial
weights, active-support isolation, and calibrated binary-block edge cases.
"""
from pathlib import Path
from itertools import combinations_with_replacement, product
from collections import defaultdict
import ast, hashlib, json, math
import sympy as s

ROOT = Path(__file__).resolve().parents[1]

def expression(text, env):
    def go(n):
        if isinstance(n, ast.Constant) and type(n.value) is int: return s.Integer(n.value)
        if isinstance(n, ast.Name): return env[n.id]
        if isinstance(n, ast.UnaryOp) and isinstance(n.op, ast.USub): return -go(n.operand)
        if isinstance(n, ast.BinOp):
            a, b = go(n.left), go(n.right)
            if isinstance(n.op, ast.Add): return a+b
            if isinstance(n.op, ast.Sub): return a-b
            if isinstance(n.op, ast.Mult): return a*b
            if isinstance(n.op, ast.Pow) and b.is_Integer and 0 <= b <= 4: return a**int(b)
        raise ValueError(ast.dump(n))
    return go(ast.parse(text, mode='eval').body)

def majorant():
    A,C,i,D,k = s.symbols('A C i D k')
    L=C*D+1-A; F=1+k*k*D*D*(D-1); G=A+F*L; Ns=2*G+L
    N1=2*k*k*D*(D-1)*L+3*C; N2=2*k*k*(D-1)*L
    N3=2*k*k*(L-C); N4=2*k*k*C
    T6=k*((1024*D*D-512*D-128)*Ns-64*N1-40*N2-28*N3-21*N4)
    B8=8*D*D-4*D-1
    collected=k*(128*B8*Ns-8*k*k*(2*B8+2*D-1)*L+C*(14*k*k-192))
    assert s.expand(T6-collected)==0
    t7=2048*D**7-1024*D**6-256*D**5-128*D**4-80*D**3-56*D**2-42*D-33
    remainder=109824*D**6+36608*D**5+18304*D**4+9984*D**3+5460*D**2+2772*D+1089
    assert s.expand(t7*t7-2048**2*D**13*(D-1)-remainder)==0
    assert 2048 > 1024+256+128+80+56+42+33
    E7=14*k**3*(A-1)/D-9*k**3*C/D+9*k**3*(A-1)/D**2-33*k**3*C/D**2+33*k**3*(A-1)/D**3
    E7+=k*((120*C+192-64*A)/D+(84*C+120-40*A)/D**2+(63*C+84-28*A)/D**3+(63-21*A)/D**4)
    E7+=s.Rational(99,2)*k*C/D**4+s.Rational(33,2)*k*(3-A)/D**5
    assert s.expand(2*D**5*T6-k*t7*Ns-2*D**5*E7)==0
    J=4*A-5; S=A*A-1; d=S*C*C+1
    assert s.expand(J**3-(A+1)*(64*A*A-304*A+604)+729)==0
    assert s.expand(J**3-S*(64*A-240)-(364*A-365))==0
    # Each positive coefficient after A=729+a proves the relevant inequality
    # throughout the infinite real half-line, not only at sampled integers.
    a=s.Symbol('a')
    positive_numerators={
      '729/(A+1)<1': A+1-729,
      '(364A-365)/(A^2-1)<1': S-(364*A-365),
      '(A+1)(A^2-1)>A^3': (A+1)*S-A**3,
      '64A^3/(A^2-1)^2<1': S*S-64*A**3,
      'JA/(A^2-1)<4': 4*S-J*A,
    }
    positive_certificates={}
    for name,pol in positive_numerators.items():
        shifted=s.Poly(s.expand(pol.subs(A,a+729)),a)
        assert all(x>0 for x in shifted.all_coeffs())
        positive_certificates[name]=[int(x) for x in shifted.all_coeffs()]
    assert s.Rational(64)+s.Rational(40,9)+s.Rational(28,81)+s.Rational(21,729)<69
    assert s.Rational(66,9**4)<1
    assert 14*64+33==929 and 1024>929 and 288>277
    correction=i**3*(9*C*C*(64*A-239)-14*C*(64*A*A-304*A+603)+1024)+288*i+2048
    subs={k:i*J*C,D:d}
    # Simultaneous substitution avoids treating abbreviation D as a variable.
    TT=s.expand((T6+correction).subs(subs, simultaneous=True))
    FF=s.expand(F.subs(subs, simultaneous=True)); GG=s.expand(G.subs(subs, simultaneous=True))
    delta=s.Poly(s.expand(TT*TT-2048**2*d*FF*GG*GG),A,C,i)
    expected=json.loads((ROOT/'nine/REFINED_DEFECT_POLYNOMIAL.json').read_text())
    assert {tuple(z['powers']):z['coefficient'] for z in expected['terms']}==dict(delta.terms())
    # A monomial A^a C^c i^j has weight (a+c)r+4an+2a+j.
    # These three coordinate bounds prove dominance for EVERY r,n>0.
    leaders=[]
    for (aa,cc,ii),co in delta.terms():
        assert aa+cc<=33 and aa<=15 and 2*aa+ii<=36
        if (aa+cc,aa,2*aa+ii)==(33,15,36): leaders.append(((aa,cc,ii),int(co)))
    assert leaders==[((15,18,6),9*2**18)]
    supportT=s.expand((T6+256*i*(k*k+2)+2048).subs(subs, simultaneous=True))
    supportdelta=s.Poly(s.expand(supportT*supportT-2048**2*d*FF*GG*GG),A,C,i)
    supportleaders=[]
    for (aa,cc,ii),co in supportdelta.terms():
        assert aa+cc<=35 and aa<=17 and 2*aa+ii<=40
        if (aa+cc,aa,2*aa+ii)==(35,17,40):supportleaders.append(((aa,cc,ii),int(co)))
    assert supportleaders==[((17,18,6),2**30)]
    radical_id=s.symbols('theta omega x y')
    theta,omega,x,y=radical_id
    norm=(theta*theta-omega*omega*(x*x+y*y))**2-4*omega**4*x*x*y*y
    assert s.expand(norm-s.prod(theta-omega*(sx*x+sy*y) for sx,sy in product((-1,1),repeat=2)))==0
    return dict(identity_checks=7, expanded_defect_terms=len(delta.terms()),
      positive_half_line_certificates=positive_certificates,
      defect_leader={'A':15,'C':18,'i':6,'coefficient':9*2**18},
      defect_degree='33*r+60*n+36',final_degree='154*r+328*n+4*c+196',
      final_diagonal_leader='81*2^148*kappa^4*rho^154*nu^328',
      inherited_support_majorant={'defect_terms':len(supportdelta.terms()),'defect_degree':'35*r+68*n+40','final_degree':'158*r+344*n+4*c+204','final_diagonal_leader':'2^172*kappa^4*rho^158*nu^344'},
      dominance='All r>0,n>0; leading coordinates uniquely saturate three bounds.')

def sources():
    oldpath=ROOT/'source/data/source_system60.json'; old=json.loads(oldpath.read_text())
    new=json.loads((ROOT/'source/selective12_source.json').read_text())
    assert hashlib.sha256(oldpath.read_bytes()).hexdigest()==new['source_sha256']
    variables=s.symbols(' '.join(old['variables'])); ports=s.symbols(' '.join(old['constants']))
    env=dict(zip(old['variables'],variables)); env.update(zip(old['constants'],ports))
    shift=set(new['shifted_coordinates']); assert len(shift)==12
    for name in shift: env[name]+=1
    def get(x):return s.Integer(x) if type(x)is int else env[x]
    for name,op,a,b in old['source']:
        aa,bb=get(a),get(b);env[name]={'*':lambda:aa*bb,'+':lambda:aa+bb,'-':lambda:aa-bb}[op]()
    penv=dict(zip(old['constants'],ports)); records=0
    byrow={}
    for (aa,bb),row in zip(old['comparisons'],new['rows']):
        expected=s.Poly(s.expand(get(aa)-get(bb)),*variables)
        actual={tuple(t['alpha']):s.expand(expression(t['coefficient'],penv)) for t in row['terms']}
        assert dict(expected.terms())==actual
        for t in row['terms']:
            alpha=t['alpha'];f=math.factorial(2-sum(alpha))*math.prod(math.factorial(a) for a in alpha)
            assert s.expand(expression(t['weighted_coefficient'],penv)-f*expression(t['coefficient'],penv))==0
        records+=len(actual);byrow[row['original_row_one_based']]=row
    assert records==109
    certificates=[]
    for path in sorted((ROOT/'packing').glob('CERTIFICATE_*_selective12_*.json')):
        t=json.loads(path.read_text());ws=t['weights'];p=t['padding_exponent'];W=t['maximum_weight']
        assert len(ws)==len(set(ws))==31 and p not in ws and min(ws)>=0 and W==max([p]+ws)
        padded=[]
        for count in range(3):
            for inds in combinations_with_replacement(range(31),count):
                alpha=tuple(inds.count(i) for i in range(31))
                padded.append(((2-count)*p+sum(ws[i] for i in inds),alpha))
        assert len(padded)==528
        targets={r['target_exponent']:r['original_row_one_based'] for r in t['rows']}
        assert len(targets)==22
        checks=0;degree=-1;degree_terms=[]
        for row in t['rows']:
            ix=row['original_row_one_based']; sign=t['coefficient_signs'][ix-1]
            original={tuple(z['alpha']):z for z in byrow[ix]['terms']}
            for term in row['terms']:
                alpha=tuple(term['alpha']);e=term['encoding_exponent']
                assert e==row['target_exponent']-(2-sum(alpha))*p-sum(a*w for a,w in zip(alpha,ws)) and e>=0
                assert s.expand(expression(term['weighted_coefficient'],penv)-sign*expression(original[alpha]['weighted_coefficient'],penv))==0
                for code,gamma in padded:
                    if e+code in targets:assert targets[e+code]==ix and gamma==alpha
                    checks+=1
                if e>degree: degree=e;degree_terms=[term]
                elif e==degree:degree_terms.append(term)
        assert degree==t['Dmax'] and t['Kcode']==degree+2*W and t['Kcode']>=max(targets)+2
        top=s.expand(sum(expression(z['weighted_coefficient'],penv) for z in degree_terms))
        assert top.is_Integer and top>0
        E=W+t['Kcode']+2;hc=E+W+23
        n=hc-15;tau=n//2;rem=n%2;assert tau>=0
        r,c=4*E+2,2*W+1
        certificates.append(dict(file=path.name,comparisons=checks,W=W,K=t['Kcode'],E=E,
          source_R_degree=r,source_N_degree=n,cap_degree=c,final_degree=154*r+328*n+4*c+196,
          source_R_leader=f'4*lambda^{2*E}',source_N_leader=f'2^({15+rem}*kappa/2-10)*lambda^{tau}',source_N_b_remainder=rem))
    return dict(affine_rows_verified=22,factorial_records_verified=records,certificates=certificates)

def binary_edges():
    checks=0
    # Exhaust every S,T fitting a binary block, including zero and all-carry
    # extremes, and permit S+T>=L only as a deliberately excluded comparison.
    for ell in range(1,8):
        L=1<<ell
        for S in range(L):
            for T in range(L-S):
                R=L*L+(S+T)*L+L-1-S
                threshold=1+ell+T.bit_count()
                assert R.bit_count()==1+ell+(S+T).bit_count()-S.bit_count()
                assert (R.bit_count()>=threshold)==((S&T)==0)
                checks+=1
    borrow_checks=0
    for B in [8,16,32,64,128]:
        for h in range(-B//4+1,B//4):
            for carry in [-1,0]:
                for target in [0,1]:
                    raw=2*h+target+carry;out,digit=divmod(raw,B)
                    assert out in [-1,0]
                    if target: assert ((digit&(B-2))==0)==(h==0)
                    borrow_checks+=1
    # Actual-mask exponent parity: odd 31-coordinate correction becomes even
    # because block length is L=2b*B^E, unlike the integer-only L=B^E route.
    for kappa in [2,4,8,100]:
        for E,W in [(4596,174),(5000,170)]:
            for k in range(8):
                v=kappa+2*k;ell=1+k+E*v
                mask_pop=(W+23)*v-31*k-22
                exponent=1+ell+mask_pop
                assert exponent==kappa*(E+W+23)+(2*(E+W+23)-30)*k-20
                assert exponent%2==0
    return dict(binary_block_cases=checks,signed_borrow_cases=borrow_checks,includes_b_equal_one=True)

def main():
    if not __debug__:raise RuntimeError('Assertions must be enabled')
    out={'status':'PASS','scope':'Independent finite identities and source interfaces, not an end-to-end formal proof.'}
    out['majorant']=majorant();out['source']=sources();out['binary_edge_cases']=binary_edges()
    (ROOT/'audit/INDEPENDENT_ARITHMETIC_VERIFICATION.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
