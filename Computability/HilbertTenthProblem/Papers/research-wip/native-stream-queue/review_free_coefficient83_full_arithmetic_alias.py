#!/usr/bin/env python3
"""Independent pinned-data proof/source review; giant Pell witnesses are not evaluated."""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

AUTHOR_PINS = {
 'free_coefficient83_full_arithmetic_alias.py': 'f8330749b8162127405802ee267a26a4e86f97729aa7864e9a35ddfac964777a',
 'free_coefficient83_full_arithmetic_alias.json': '0cef01d7d4ae36c0f50e31dc514f442edfd8764103c2de9cb38a7ed326f40f44',
 'free_coefficient83_full_arithmetic_alias.md': 'da52e1ee7c33cae2f642a343b38d467b676fa94a4ff24d969f99b166d32f60a9',
}
DATA_PINS = {
 'complete83_free_coefficient_scout.json': '682d37d4cedcd3c4a086ed3a2e55f272892670edb0424fc0fd8242337f1bf016',
 'complete83_free_coefficient_scout.md': '867e277a2ca09af392e81cf7e54f6eaa7677a939ea3717448cd89053b5690b31',
 'free_coefficient83_native_alias.md': '542775d7ff0ccd84f5fe94c32d6c396ad45a8cc033dd1cbd37ed72dedd40f96f',
 'first_index_scaled_obstruction.md': 'b67d208d4c18e45145cf91f272d72e2852c09d79be631da8f0a0ce5f377ba1fd',
 '../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
}
FACTORS = ['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']


def check(ok, message):
    if not ok: raise ValueError(message)


def digest(data): return hashlib.sha256(data).hexdigest()


def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


class P:
    """Exact sparse polynomial, with repeated variable names as monomials."""
    def __init__(self,value=0):
        if isinstance(value,P): self.c=value.c
        elif type(value) is int: self.c={():value} if value else {}
        else: self.c={m:v for m,v in value.items() if v}
    def __add__(self,other):
        other=P(other);out=dict(self.c)
        for m,v in other.c.items(): out[m]=out.get(m,0)+v
        return P(out)
    __radd__=__add__
    def __neg__(self): return P({m:-v for m,v in self.c.items()})
    def __sub__(self,other): return self+-P(other)
    def __rsub__(self,other): return P(other)+-self
    def __mul__(self,other):
        other=P(other);out={}
        for a,x in self.c.items():
            for b,y in other.c.items():
                m=tuple(sorted(a+b));out[m]=out.get(m,0)+x*y
        return P(out)
    __rmul__=__mul__
    def __pow__(self,n):
        check(type(n) is int and n>=0,'polynomial exponent')
        out=P(1);base=self
        while n:
            if n&1: out=out*base
            base=base*base;n//=2
        return out
    def __eq__(self,other): return self.c==P(other).c
    def saved(self): return [[list(m),v] for m,v in sorted(self.c.items())]


def var(name): return P({(name,):1})


class Q:
    """Rational functions, with normalization only at independently proved cuts."""
    def __init__(self,n=0,d=1):
        if isinstance(n,Q): self.n,self.d=n.n,n.d
        else: self.n,self.d=P(n),P(d)
        check(bool(self.d.c),'zero formal denominator')
    def __add__(self,other):
        other=Q(other)
        if self.d==other.d: return Q(self.n+other.n,self.d)
        return Q(self.n*other.d+other.n*self.d,self.d*other.d)
    __radd__=__add__
    def __neg__(self): return Q(-self.n,self.d)
    def __sub__(self,other): return self+-Q(other)
    def __rsub__(self,other): return Q(other)+-self
    def __mul__(self,other):
        other=Q(other);return Q(self.n*other.n,self.d*other.d)
    __rmul__=__mul__
    def __eq__(self,other):
        other=Q(other);return self.n*other.d==other.n*self.d


def formal_source(packet):
    names='beta J X Y k c D tau F Z x ell b K MC MF W kap mu f S V y'.split()
    z={name:var(name) for name in names}
    beta,J,X,Y,k,c,D,tau,F,Z,x,ell,b,K,MC,MF,W,kap,mu,f,S,V,y=(z[n] for n in names)
    q=beta*J+1;E=X*Y;a=Y*(X+1);Delta=(a+1)*(a+3);H=4*a+3
    R=(q*q-q*F-Z)*(q*q-1)+(MC+q*MF)*J
    C=Z+W;u=ell*x+b
    gamma=Q(D-a*c-X,H);rho=Q(mu-a*kap-W,H)
    tp=(K*q+X)*C+(q-F)*q
    env={
      'Bm1':Q(beta),'Jrep':Q(J),'w':Q(X,q),'s':Q(Y,q**3),
      'tau_root':Q(tau),'eta':Q(c-k*Y),'zeta':Q(k-c+k*Y),
      'rho':rho,'sigma':Q(D-a*c-X-mu+a*kap+W,H),
      'F':Q(F),'Z':Q(Z),'x':Q(x),'Kconstant':Q(K),'MC':Q(MC),'MF':Q(MF),
      'twice_cell_bits':Q(ell),'inner_bits':Q(b),
      'alpha':Q(q-F-2*Z-ell*x-W),'delta':Q(kap-u,Delta),
      'h':Q(k-R-1,E),'transport_quotient':Q(tp-q,q*(q-1)),
      'f':Q(f),'aux_coefficient_root':Q(S),'y_aux':Q(y),
      'auxiliary_quotient':Q(V+c+R*f*f,c*f),
    }
    check(set(env)==set(packet['free']),'formal exact free interface')
    targets={
      'q':Q(q),'wn2':Q(X),'sn2':Q(Y),'UM':Q(E),'R10b':Q(k),
      'R10a':Q(c),'R12':Q(a),'gamma_sum':gamma,'gam':Q(D-a*c-X),
      'R14':Q(D),'A':Q(Delta),'marked_rhs':Q(C),'W':Q(W),
      'odd_index':Q(u),'index_product':Q(kap-u),'index_rhs':Q(kap),
      'modulus_multiple':Q(mu-a*kap-W),'exponent_rhs':Q(mu),
      'hpm1':Q(k-R-1),'index_difference':Q(R+1),'r_lhs':Q(R),'norm_index':Q(1),
      'kinner':Q(K*q+X,q),'innerC':Q((K*q+X)*C,q),
      'transport_partial':Q(tp,q),'local_rhs':Q(tp-q,q),'norm_transport':Q(1),
      'auxiliary_Tf':Q(V+c+R*f*f,c),'auxiliary_Tf_minus_one':Q(V+R*f*f,c),
      'auxiliary_c_Tf':Q(V+R*f*f),'aux_u_rhs':Q(V),
    }
    expected=[tau*tau-X*Y*Y*(X*Y*Y+1)*k*k,
              D*D-Delta*c*c,mu*mu-Delta*kap*kap,
              S*S*V*V-(S*S-1)*y*y,P(1),P(1),Delta*f*f-S*S]
    targets.update({name:Q(value) for name,value in zip(FACTORS,expected)})
    product=P(1)
    for value in expected: product=product*value
    targets['polynomial']=Q(product-Delta)
    dependencies={};verified=[];M=Acount=0
    for name,op,left,right in packet['source']:
        check(name not in env and op in ('+','-','*'),'literal fresh gate')
        for port in (left,right): check(type(port) is int or type(port) is str and port in env,'closed gate')
        lhs=env[left] if type(left) is str else Q(left)
        rhs=env[right] if type(right) is str else Q(right)
        value=lhs+rhs if op=='+' else lhs-rhs if op=='-' else lhs*rhs
        if name in targets:
            check(value==targets[name],'formal coefficient identity '+name)
            value=targets[name];verified.append(name)
        env[name]=value
        dependencies[name]=[v for v in (left,right) if type(v) is str]
        M+=op=='*';Acount+=op!='*'
    check(env[packet['output']]==Q(product-Delta),'whole polynomial formal identity')
    live=set();todo=[packet['output']]
    while todo:
        port=todo.pop()
        if port not in live: live.add(port);todo.extend(dependencies.get(port,[]))
    check(live==set(env),'complete gate/port liveness')
    check((M,Acount)==(46,37),'literal full ledger')
    return {'formal_variables':names,'rational_denominators':['q','q-1','H','Delta','X*Y','c*f'],
            'complete_paid_rows':83,'M':M,'A':Acount,'supplied_ports':len(packet['free']),
            'verified_cuts':verified,'factor_polynomials':[v.saved() for v in expected],
            'full_output_monomials':len((product-Delta).c),
            'full_output_polynomial_sha256':digest(json.dumps((product-Delta).saved(),separators=(',',':')).encode()),
            'scope':'Exact formal rational pullback; Pell specialization and positivity proved in note, not giant numerical evaluation'}


def matrix_product(a,b,m):
    return ((a[0]*b[0]+a[1]*b[2])%m,(a[0]*b[1]+a[1]*b[3])%m,
            (a[2]*b[0]+a[3]*b[2])%m,(a[2]*b[1]+a[3]*b[3])%m)


def psi_mod(A,n,m):
    out=(1,0,0,1);base=(2*A%m,-1%m,1,0)
    while n:
        if n&1: out=matrix_product(out,base,m)
        base=matrix_product(base,base,m);n//=2
    return out[2]


def inverse(a,m):
    old_r,r=a,m;old_s,s=1,0
    while r:
        q=old_r//r;old_r,r=r,old_r-q*r;old_s,s=s,old_s-q*s
    check(old_r==1,'reduced CRT inverse');return old_s%m


def finite_arithmetic(author):
    t=9159759548913079;p=t*(t+2);n=t*(t+1);R=2*n-1
    B=512;q=B**3;J=(q-1)//(B-1);MC,MF0=374,292;MF=MF0+B-1
    K,F,Z,alpha=135578,64816286,17584025,25844766
    W=q-F-2*Z-alpha-18;C=W+Z;G=q*q-q*F-Z
    check(R==G*(q*q-1)+(MC+q*MF)*J,'actual packed index')
    check(W==2**23 and C==25972633,'input and alpha identity')
    check(F+Z<q and (2*q-1)*(q*q-1)<R<q**4-q**3,'range interface')
    check(MC%4==2 and MF0%8==4 and 0<MC<B-1 and 0<MF0<B-1,'mask residues/ranges')
    check(MC.bit_count()+MF0.bit_count()==9,'population interface')
    check(0<K<B*B and 0<K%B<B and 0<K//B<B,'positive bounded program ports')
    wm=pow(2,p-27,q-1)
    check(wm==4096 and ((K+wm)*C+q-F-1)%(q-1)==0,'transport numerator divisibility')
    residues={}
    for m in [p,4*p]:
        am=(pow(2,t+1,m)*(pow(2,p,m)+1)+2)%m
        residues[m]=psi_mod(am,p,m)
    g=gcd(residues[4*p],4*p)
    check(g==gcd(residues[p],p)==3 and (p-R)%g==0,'noncoprime CRT compatibility')
    j=((p-R)//g)*inverse(residues[4*p]//g,4*p//g)%(4*p//g)
    check((R+residues[4*p]*j)%(4*p)==p,'CRT index coefficient')
    result={'p':p,'n':n,'R':R,'G':G,'q':q,'J':J,'MF':MF,'W':W,'C':C,'alpha':alpha,
            'w_mod_repunit':wm,'c_mod_p':residues[p],'c_mod_4p':residues[4*p],
            'gcd_c_p':g,'auxiliary_CRT_coefficient':j,'DC':K%B,'DR':K//B,
            'input_exponent':23,'positive_input_bound':2<3,'main_index_not_packed':p!=R,
            'recipe_b_d_failure':9%5!=0,'recipe_d_power5_failure':9 not in (1,5,25),
            'giant_witnesses_materialized':False}
    for name,value in result.items():
        if name in author: check(exact(value,author[name]),'author finite datum '+name)
    check(t>=11 and t%2==1 and p%4==3 and p>23 and t+1>81,'scaled theorem premises')
    check(p-27>0,'positive scale exponent')
    return result


def verify(root,author_root):
    for folder,pins in [(root,DATA_PINS),(author_root,AUTHOR_PINS)]:
        for name,pin in pins.items(): check(digest((folder/name).read_bytes())==pin,'pin '+name)
    author=json.loads((author_root/'free_coefficient83_full_arithmetic_alias.json').read_text())
    packet=json.loads((root/'complete83_free_coefficient_scout.json').read_text())['packet']
    check(packet['factors']==FACTORS,'factor order')
    return {'status':'PASS','review_source_sha256':digest(Path(__file__).read_bytes()),
            'author_pins':AUTHOR_PINS,'data_pins':DATA_PINS,
            'finite_arithmetic':finite_arithmetic(author['outer_case']),
            'formal_complete_source':formal_source(packet),
            'conclusion':'Proof-defined full positive diagnostic zero with intended factors and p != R; valid compiler recipe absent',
            'universal_bound_claim':False,'giant_zero_numerically_evaluated':False,
            'author_or_historical_python_executed':False}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',required=True,type=Path)
    p.add_argument('--author-root',type=Path)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=p.parse_args();result=verify(a.root,a.author_root or a.root)
    data=json.dumps(result,sort_keys=True,indent=2)+'\n'
    check(exact(result,json.loads(data)),'typed receipt roundtrip')
    if a.expect: check(exact(result,json.loads(a.expect.read_text())),'saved receipt')
    else: a.output.write_text(data)
    print('PASS: independent finite CRT/packing and complete 83-row formal source pullback; diagnostic recipe only')


if __name__=='__main__': main()
