#!/usr/bin/env python3
"""Bounded read-only intake: authenticate ZIP text/data; execute no ZIP code."""
import argparse
import hashlib
import json
import math
import zipfile
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run this assertion-based independent audit without -O.')
PINS = {'Failure_of_Positive_Index_Restoration_Package.zip': {'archive': '78dfb46d6e5a620dc818a0cf9da497930c45c80e092d8054bb98508bc050a456', 'members': {'Research_Report33/README.md': 'a4036fbac014e3bb8042bd9108c44da50cb8dc4c644b78f6f68ad413e58183cf', 'Research_Report33/Research_Report33.tex': 'b049e6ec8608a704a53983182511da8e873f9c5842680af63bdbed492d5ed9f6', 'Research_Report33/repro/evidence/FULL-SIGNED-COUNTEREXAMPLE.md': 'b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd', 'Research_Report33/repro/evidence/RAW-POSITIVE-REDUCTION.md': '0ae2f56e7db3177f3100198ae503c950d2f11d30d3d6d55d51f399dbdbeb48a9', 'Research_Report33/supplements/evidence/GENERALIZED-COMPILER-SUPPLEMENT.md': '69f64c16aed4f9b962ec82553186ffc25cae79cb6808bfe0a3e6136797c0ae60', 'Research_Report33/repro/sources/complete74_nonlinear_index_projection_scout.json': 'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92', 'Research_Report33/repro/sources/complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'Research_Report33/repro/sources/complete75_signed_projection_elimination101.md': '55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d', 'Research_Report33/repro/sources/complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117'}}, 'Entire_Native_Witness_Fiber_Package.zip': {'archive': 'c8821ab95a5c94730ee6634924e00d11ad9650ec76af89d7f73a48d3653fe3d6', 'members': {'entire-native-fiber-report25/README.md': 'a7ff53a20e1126bfff3fe295f9f3fe4d77825c2e4d262bb3e64c6af9643a23ca', 'entire-native-fiber-report25/proofs/entire-fiber/THEOREM.md': '6a7e6d941175fb14025b84a3d06788d6c2a995cdea2c2009e4f4f558ce58cd8c', 'entire-native-fiber-report25/source/native_blocks.json': 'a3ef38c5a449040a817384d564da90a5b7a440d426997df8ae6acecc4d55d74f'}}, 'Canonical_Histories_and_Infinite_Fibers_Package.zip': {'archive': '6abeadd97bb910dfc7330932d52fefd1dc14ef530489a7e11721dcf4381f8e5f', 'members': {'canonical-fiber-release-20261003/README.md': '5657032fc5a7f5f965fd1c32cdeb10c18ae64c0b9d74d19b2e188c7aa292354f', 'canonical-fiber-release-20261003/native-fibers/THEOREM.md': 'ac0ce327330d36c55916ec188b2f80903606018239eaddc49d34636782a70aae'}}}
CURRENT = {'complete74_nonlinear_index_projection_scout.json': 'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92', 'complete74_factored_first_norm.json': '7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28', 'complete75_signed_projection_elimination101.md': '55b701410d05b515b6cbc4619a3f39fc290f469d21d03dfee9e291aa674fa31d', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b', 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d', 'review_complete74_nonlinear_index_bootstrap.md': '4922eb2587fa1ecda313792ea0644c6da123b5ebdb86a0dbdfa02671d48ed1a8', 'complete74_negative_index_refinement.md': 'a471a60a2b742e8d84ad9c19c333e6c7949e5da911c5b1149eded0854d3fbc99'}


def sha(b): return hashlib.sha256(b).hexdigest()
def typed(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(typed(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(typed(x,y) for x,y in zip(a,b))
    return a==b

class P:
    def __init__(self,d): self.d={m:c for m,c in d.items() if c}
    @staticmethod
    def atom(n): return P({(n,):1})
    @staticmethod
    def of(a): return a if isinstance(a,P) else P({():a})
    def __add__(self,b):
        d=dict(self.d)
        for m,c in self.of(b).d.items(): d[m]=d.get(m,0)+c
        return P(d)
    __radd__=__add__
    def __neg__(self): return P({m:-c for m,c in self.d.items()})
    def __sub__(self,b): return self+-self.of(b)
    def __rsub__(self,b): return self.of(b)+-self
    def __mul__(self,b):
        d={}
        for m,c in self.d.items():
            for n,e in self.of(b).d.items():
                k=tuple(sorted(m+n));d[k]=d.get(k,0)+c*e
        return P(d)
    __rmul__=__mul__
    def __pow__(self,k):
        r=P.of(1)
        for _ in range(k): r=r*self
        return r
    def __eq__(self,b): return self.d==self.of(b).d


def source_interface(packet):
    names=['q','X','Y','k','c','a','D','Delta','H','C','W','kappa','mu','R','J','F','Z','alpha','ell','x','b','K0','MC','MFsrc','z','eta','zeta','rho','sigma','delta','tau','i','f','h','o','j','y','w','s','Bm1']
    v={n:P.atom(n) for n in names}
    mapping={'q':'q','wn2':'X','sn2':'Y','R10b':'k','R10a':'c','R12':'a','R14':'D','A':'Delta','a4m5':'H','marked_rhs':'C','W':'W','index_rhs':'kappa','exponent_rhs':'mu','restored_r':'R','Jrep':'J','Kconstant':'K0','twice_cell_bits':'ell','inner_bits':'b','MF':'MFsrc','zquot':'z','y_aux':'y'}
    cuts={k:v[n] for k,n in mapping.items()}
    cuts['repunit']=v['q']-1
    rows={n:(op,a,b) for n,op,a,b in packet['source']}
    def expansion(target,expand_target=False):
        memo=dict(cuts)
        if expand_target: memo.pop(target,None)
        if target=='q': memo.pop('repunit',None)
        def at(t):
            if type(t) is int: return P.of(t)
            if t not in memo:
                if t not in rows: memo[t]=v.get(t,P.atom(t))
                else:
                    op,a,b=rows[t];a,b=at(a),at(b)
                    memo[t]=a*b if op=='*' else a+b if op=='+' else a-b
            return memo[t]
        return at(target)
    q,X,Y,k,c,a,D,deltaD,H,C,W,kap,mu,R,J,F,Z,alpha,ell,x,b,K0,MC,MF,z,eta,zeta,rho,sigma,delta,tau,i,f,h,o,j,y,w,s,bm=[v[n] for n in names]
    definitions={
      'q':bm*J+1,'wn2':w*q**3,'sn2':s*q**3,'R10b':eta+zeta,
      'R10a':k*Y+eta,'R12':X*Y+Y,'a4m5':4*a+3,'A':a*a+H,
      'R14':X+a*c+(rho+sigma)*H,'marked_rhs':q-alpha-ell*x,
      'W':C-Z,'index_rhs':ell*x+b+delta*deltaD,
      'exponent_rhs':W+a*kap+rho*H,'restored_r':k-h*X*Y-1,
    }
    for name,expected in definitions.items(): assert expansion(name,True)==expected,name
    expected=[(K0+X)*C-F-z*(q-1),
      R-((q*q-Z-q*F)*(q*q-1)+(MC+q*MF)*J),
      X*Y*Y*(X*Y*Y+1)*k*k-tau*tau+1,
      D*D-deltaD*c*c-1,i*i*c**4-deltaD*(f*f-1),
      i*i*c**4*((j*c-R)**2-y*y)-1+y*y,j*c-R-o*f+c,
      mu*mu-deltaD*kap*kap-1]
    assert len(packet['comparisons'])==8
    for (l,r),e in zip(packet['comparisons'],expected): assert expansion(l)-expansion(r)==e,(l,r)
    expected_w=['Jrep','F','alpha','zquot','f','h','i','j','o','s','w','tau','eta','zeta','y_aux','Z','delta','rho','sigma']
    assert packet['mode']=='signed20' and packet['witnesses']==expected_w
    tail=[]
    for k,(l,r) in enumerate(packet['comparisons']):
        tail += [[f'residual_{k}','-',l,r],[f'square_{k}','*',f'residual_{k}',f'residual_{k}']]
    for k in range(1,8): tail.append([f'sum_{k}','+','square_0' if k==1 else f'sum_{k-1}',f'square_{k}'])
    assert packet['polynomial_source']==packet['source']+tail
    return {'triangular_definitions':len(definitions),'all_actual_residuals':8,'witnesses':19,'full_SOS_finalizer_gates':len(tail),'full_operations':len(packet['polynomial_source'])}


def pell(A,n):
    x,y=1,0
    for _ in range(n): x,y=A*x+(A*A-1)*y,x+A*y
    return x,y

def prime(n):
    if n<2: return False
    return all(n%p for p in range(2,math.isqrt(n)+1))

def order2(n):
    t,x=1,2%n
    while x!=1: x=x*2%n;t+=1
    return t


def independent_checks():
    # One independently found toy scale/CRT fixture. It is not a compiler export.
    d,b,x,K0,MC,MF=1,1,1,0,-2,5
    t,p0=2,7;B=2**d;q=2**t;J=(q-1)//(B-1);X=2**p0;Q=q*q-1
    D0=4*q**3*(X+1)//3
    assert q>2*d*x+1 and p0>3*t and p0%12==7 and math.gcd(p0,2*t)==1
    assert math.gcd(X+1,Q)==3 and (X+1)%9==3 and math.gcd(D0,Q)==1
    s0=next(s for s in range(1,Q) if math.gcd(s,Q)==math.gcd(1+D0*s,Q)==1)
    hit=next(k for k in range(100) if prime(1+D0*(s0+Q*k)))
    s=s0+Q*hit;ell=1+D0*s;Y=s*q**3;E=X*Y;a=Y*(X+1);A=a+2;H=4*a+3;Delta=A*A-1
    O=order2(H);T=math.lcm(4,2*E,O);L=E//2
    assert ell%3==2 and H==3*ell and math.gcd(Q*H,T)==1
    assert math.gcd(Q*H,2*E)==1 and math.gcd(Q*H,O)==1
    assert (2*(ell-1))%O==0
    C=1;alpha=q-1-2*d*x;F=K0+X-q+1;u=2*d*x+b;mu,kappa=pell(A,u);eu=mu-a*kappa
    assert (kappa-u)%Delta==0 and kappa>u
    delta=(kappa-u)//Delta;M=(MC+q*MF)*J
    residue=(-M-Q*(q*q-q*F+eu-1))%(Q*H)
    p=p0+T*((residue-p0)*pow(T,-1,Q*H)%(Q*H))
    step=T*Q*H
    for _ in range(3):
        if p>0 and q*q-q*F+(p+M)//Q>1: break
        p+=step
    assert p%T==p0%T and p%(Q*H)==residue
    Z=q*q-q*F+(p+M)//Q;rho=(Z+eu-1)//H;W=1-Z
    assert min(J,alpha,F,s,delta,Z,rho)>0 and W<0
    assert q-alpha-2*d*x==C and (K0+X)*C==F+(q-1)
    assert (q*q-Z-q*F)*Q+M==-p
    assert mu==W+a*kappa+rho*H and mu*mu-Delta*kappa*kappa==1
    assert pow(2,p,H)==X%H and p%4==3
    n0=((1-p0)//2)%L
    assert (2*n0+p-1)%E==0
    # Generalized exponent selection: even/odd t, including factors2,3 and7.
    exponent_checks=0
    for tt in range(1,49):
        t0=tt
        for factor in (2,3):
            while t0%factor==0:t0//=factor
        pp=next(7+12*k for k in range(4*tt+10) if (7+12*k)%t0==1%t0 and 7+12*k>3*tt)
        qq=2**tt;xx=2**pp;DD=4*qq**3*(xx+1)//3
        assert math.gcd(pp,2*tt)==1 and math.gcd(xx+1,qq*qq-1)==3
        assert (xx+1)%9==3 and math.gcd(DD,qq*qq-1)==1
        exponent_checks+=1
    # Small negative-target auxiliary fixture, not an outer/compiler zero.
    AA,pp=2,3;DD,cc=pell(AA,pp);dis=AA*AA-1;mm=cc*pp;ff,psi=pell(AA,mm);RR=dis*psi
    assert RR%(cc*cc)==0
    nn=pp+2*mm;xxaux,yy=pell(RR,nn);assert xxaux%RR==0
    UU=xxaux//RR;assert (UU-pp)%cc==0 and (UU+cc)%ff==0
    ii=RR//(cc*cc);jj=(UU-pp)//cc;oo=(UU+cc)//ff
    assert min(ii,jj,oo,yy)>0
    assert (ii*cc*cc)**2==dis*(ff*ff-1)
    assert UU==jj*cc+pp==oo*ff-cc
    assert RR*RR*(UU*UU-yy*yy)==1-yy*yy
    # Ordinary whole-fiber progression, independently checked conditionally on p|m.
    divisibility=0
    for AA in range(2,7):
      pp=3;dd,cc=pell(AA,pp);dis=AA*AA-1;g=math.gcd(cc,dis)
      assert g==math.gcd(pp,dis)
      for kk in range(1,2*cc+1):
        xx0,yy0=pell(AA,pp*kk)
        assert (dis*yy0%(cc*cc)==0)==(kk%(cc//g)==0)
        divisibility+=1
    # The normalized progression is stricter when g>1; do not transfer it blindly.
    cc=pell(2,3)[1]; m0=3*cc//math.gcd(cc,3);yy0=pell(2,m0)[1]
    assert (3*yy0)%(cc*cc)==0 and yy0%(cc*cc)!=0
    return {'toy_outer_CRT':{'compiler_export':False,'q':q,'p0':p0,'ell':ell,'s':s,'H':H,'order2':O,'progression_step_bits':step.bit_length(),'positive_Z_rho':True,'negative_W':True,'main_first_ratio_hit_materialized':False},
      'generalized_exponent_cases':exponent_checks,
      'negative_target_auxiliary_only':{'A':2,'p':3,'m':mm,'n':nn,'largest_bits':max(z.bit_length() for z in (ff,UU,yy)),'full_compiler_zero':False},
      'ordinary_fiber_divisibility_checks':divisibility,
      'ordinary_vs_normalized_scope_fixture':{'A':2,'p':3,'c':cc,'ordinary_m0':m0,'normalized_m0':3*cc,'full_padded_native_zero':False}}


def verify(repo):
    repo=Path(repo);archive_members={}
    for name,item in PINS.items():
        p=repo/'docs/incoming'/name;b=p.read_bytes();assert sha(b)==item['archive'],name
        with zipfile.ZipFile(p) as z:
            assert len(z.namelist())==len(set(z.namelist()))
            for member,digest in item['members'].items():
                data=z.read(member);assert sha(data)==digest,(name,member);archive_members[(name,member)]=data
    wip=repo/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
    for name,digest in CURRENT.items(): assert sha((wip/name).read_bytes())==digest,name
    arc='Failure_of_Positive_Index_Restoration_Package.zip'
    matched=[]
    for name in ['complete74_nonlinear_index_projection_scout.json','complete74_factored_first_norm.json','complete75_signed_projection_elimination101.md','complete75_half_binomial_compiler.md']:
        assert archive_members[(arc,'Research_Report33/repro/sources/'+name)]==(wip/name).read_bytes();matched.append(name)
    receipt=json.loads((wip/matched[0]).read_text());signed=next(f['packet'] for f in receipt['forms'] if f['packet']['mode']=='signed20')
    # Exact current85 structural separation: its marked C contains F+Z and index is a retained factor.
    new85=json.loads((wip/'complete85_auxiliary_bezout_projection.json').read_text())['packet'];rows={r[0]:r for r in new85['source']}
    assert rows['q_minus_FZ']==['q_minus_FZ','-','q_minus_F','Z']
    assert rows['C_after_alpha']==['C_after_alpha','-','q_minus_FZ','alpha']
    assert rows['marked_rhs']==['marked_rhs','-','C_after_alpha','scaled_t']
    assert rows['norm_index']==['norm_index','-','index_difference','r_lhs']
    assert rows['norm_product']==['norm_product','*','norm_four','norm_index']
    return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'archives':PINS,'current_pins':CURRENT,
      'exact_current_source_matches':matched,'signed19_interface':source_interface(signed),'checks':independent_checks(),
      'theorem_review':'Report33 signed19 acceptance saturation passes proof audit; raw29/positive21 remain unresolved; no conflict with normalized85.',
      'scope':'No ZIP Python/build/replay execution. No giant full child zero. No independent certification of Report25 second-term or bitlength asymptotics, PDF QA, package launchers, or canonical-height circuit costs.'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--repo',required=True);p.add_argument('--write');p.add_argument('--expect');a=p.parse_args();r=verify(a.repo)
    assert typed(r,json.loads(json.dumps(r)))
    if a.expect:assert typed(r,json.loads(Path(a.expect).read_text()))
    if a.write:Path(a.write).write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':r['status'],'theorem_review':r['theorem_review'],'interface':r['signed19_interface']}))
if __name__=='__main__':main()
