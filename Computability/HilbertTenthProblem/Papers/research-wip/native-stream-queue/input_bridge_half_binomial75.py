"""Unchanged14 input bridge and positive half-binomial converse components."""
import argparse
from collections import Counter
from math import comb
import json
from pathlib import Path
import sympy as sp
import complete75_half_binomial as candidate

prior=candidate.prior


def pell(A,n,mod=None):
    D=A*A-1
    def mul(a,b):
        out=(a[0]*b[0]+D*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
        return tuple(x%mod for x in out) if mod else out
    out=(1,0);base=(A,1)
    while n:
        if n&1:out=mul(out,base)
        base=mul(base,base);n//=2
    return out


def qpoly(h,T,mod=None):
    a,b=1,4*T-3
    if not h:return a%mod if mod else a
    for _ in range(1,h):
        a,b=b,(4*T-2)*b-a
        if mod:a%=mod;b%=mod
    return b%mod if mod else b


def run(rows,env):
    env=dict(env)
    for name,op,left,right in rows:
        a=env[left] if isinstance(left,str) else left
        b=env[right] if isinstance(right,str) else right
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env


def source_check():
    full=candidate.source_audit();rows=prior.ADAPTER
    assert full['schedule'][-14:]==[list(row) for row in rows]
    counts=Counter(row[1] for row in rows)
    assert len(rows)==14 and counts['*']==7 and counts['+']==7
    z=prior.SYM;A=z['a']+2;D=A*A-1;H=4*z['a']+3
    # Use the actual shared register names rather than assuming aliases.
    env=run(prior.SCHEDULE,prior.fixed_environment(z))
    u=2*z['cell_bits']*z['x']+z['inner_bits']
    assert sp.expand(env['odd_index']-u)==0
    residuals=[z['kappa']-u-z['delta']*D,z['c']-z['kappa']-z['phi'],
               z['mu']**2-1-D*z['kappa']**2,
               z['mu']-z['W']-z['a']*z['kappa']-z['rho']*H]
    records=[]
    for offset,p in enumerate(residuals,15):
        left,right=prior.EQUALITIES[offset]
        actual=sp.expand(env[left]-env[right]);p=sp.expand(p)
        sign=1 if sp.expand(actual-p)==0 else -1
        assert sp.expand(actual-sign*p)==0
        assert sp.expand(sp.sympify(full['sources'][offset]['source'],locals=z)-p)==0
        records.append(dict(index=offset,comparison=[left,right],source=str(p),sign=sign))
    assert full['positive_witnesses']==30 and full['equations']==19
    return dict(operations=14,multiplications=7,additions=7,instructions=[list(r) for r in rows],
                input_residuals=records,complete_source_operations=75,
                complete_source_ledger=dict(outer=19,kernel=42,input=14),
                supplied_positive_input_coordinates=['kappa','mu','delta','phi','rho'],
                scope='Exact source audit; compiler theorem not established here')


def canonical_main():
    rows=[]
    for R in (3,7,11,15,19,23,31,47,51):
        r=(R-1)//2;X=2**R;den=X**r
        F,tail=divmod((X+1)**(2*r),den)
        assert F%2==0 and 0<4*tail<den
        Y=F//2;a=Y*(X+1);A=a+2;D=A*A-1;H=4*a+3;E=X*Y;P=2*X*Y*Y+1
        d,c=pell(A,R);T,k=pell(P,r+1);K=2*k
        eta=c-K*Y;zeta=K-eta;h,rem=divmod(K-R-1,E)
        gamma,remg=divmod(d-a*c-X,H)
        assert rem==remg==0 and min(eta,zeta,h,gamma)>0
        assert T*T-(E*E+X)*(K*Y)**2==1 and d*d-D*c*c==1
        assert c*den>k*(X+1)**(2*r)
        assert c*den<k*((X+1)**(2*r)+den)
        assert ((Y&-Y).bit_length()-1)==r.bit_count()-1
        rows.append(dict(R=R,X=X,Y_bits=Y.bit_length(),K_bits=K.bit_length(),c_bits=c.bit_length(),
                         all_main_quotients_positive=True))
    return dict(prototypes=rows,scope='Fresh exact main witnesses; no full compiler tuple materialized')


def input_interfaces():
    fixtures=[];representatives=0
    for q,R,indices in ((16,51,(3,)),(64,195,(3,5)),(256,771,(3,5,7))):
        X=2**R;a=2*X;A=a+2;D=A*A-1;H=4*a+3
        d,c=pell(A,R);gamma,rem=divmod(d-a*c-X,H)
        assert rem==0 and gamma>0 and 3*q+1<=R<q**4 and a>q**6
        for u in indices:
            x=(u-1)//2;b=cell_bits=1;W=2**u;C=W+1;alpha=q-C-2*x
            assert min(x,W,C,alpha)>0 and u==2*cell_bits*x+b and W<C<q
            mu,kappa=pell(A,u)
            delta,remd=divmod(kappa-u,D);phi=c-kappa;rho,remr=divmod(mu-a*kappa-W,H)
            assert remd==remr==0 and min(delta,phi,rho)>0
            assert kappa==u+delta*D and c==kappa+phi
            assert mu*mu==1+D*kappa*kappa and mu==W+a*kappa+rho*H
            fixtures.append(dict(q=q,R=R,u=u,x=x,W=W,all_input_coordinates_positive=True))
        for v in range(1,R):
            rep=pell(A,v,D)[1];expected=v if v%2 else v*A
            assert rep==expected and 0<rep<D
            if v%2==0:assert rep>=2*A>2*q
            representatives+=1
    return dict(positive_interfaces=fixtures,discriminant_representatives=representatives,
                scope='Actual new R range and recovered main norm/projection; fixed d=b=1 are interface fixtures, not compiler numerals; no first norm or Y scale asserted')


def auxiliary_checks():
    modular=0;materialized=[]
    for A in range(2,13):
        D=A*A-1
        for R in (3,7,11,15,19):
            d,c=pell(A,R);m=2*c*R
            assert pell(A,m,c*c)[1]==0
            assert qpoly((R-1)//2,0,c)==(-R)%c
            assert qpoly((R-1)//2,1-A*A)==-c
            modular+=1
    for A,R in ((2,3),(3,3),(2,7)):
        D=A*A-1;d,c=pell(A,R);m=2*c*R;f,v=pell(A,m);Aaux=D*v
        i,rem=divmod(Aaux,c*c);chi,y=pell(Aaux,R);U,remU=divmod(chi,Aaux)
        j,remj=divmod(U+R,c);o,remo=divmod(U+c,f)
        assert rem==remU==remj==remo==0 and min(i,j,o,y)>0
        assert Aaux*Aaux==D*(f*f-1)
        assert Aaux*Aaux*(U*U-y*y)==1-y*y
        assert U==j*c-R==o*f-c
        materialized.append(dict(A=A,R=R,main_c=c,auxiliary_index=m,auxiliary_base_bits=Aaux.bit_length(),
                                 all_auxiliary_coordinates_positive=True))
    return dict(modular_cases=modular,materialized=materialized,
                scope='Exact signed auxiliary identities; small full auxiliary fixtures are not compiler witnesses')


def valuations():
    cases=0
    for r in range(1,129):
        R=2*r+1;X=2**R;F=((X+1)**(2*r))//(X**r);Y=F//2
        assert F%2==0 and F%X==comb(2*r,r)%X
        val=(Y&-Y).bit_length()-1
        assert val==r.bit_count()-1==R.bit_count()-2
        for t in range(1,10):
            assert (Y%2**(3*t)==0)==(r.bit_count()>=3*t+1)
            cases+=1
    return dict(half_binomial_scale_cases=cases)


def verify():
    return dict(status='PASS_HALF_BINOMIAL_INPUT_AND_POSITIVE_CONVERSE_COMPONENTS',source=source_check(),
                main=canonical_main(),input=input_interfaces(),auxiliary=auxiliary_checks(),valuation=valuations(),
                scope='Complete75 source ledger plus bridge/converse proof components; modified compiler independently required',
                established_complete_universal_bound=75)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k!='source'},indent=2))
