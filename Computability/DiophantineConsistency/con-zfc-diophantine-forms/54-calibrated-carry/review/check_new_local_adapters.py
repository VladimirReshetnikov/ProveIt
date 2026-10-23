"""Independent exact ring/data checks for the new local adapters.

No received program is imported or executed. Symbolic expressions are built
from whitelisted literal DAG operations, never from eval of source strings.
"""
from pathlib import Path
import json,hashlib,math,gzip
import sympy as s
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parent
p=BASE/'source/data/source_system60.json'
raw=p.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48'
d=json.loads(raw); names=d['variables'];ports=d['constants']
symbols=dict(zip(names+ports,s.symbols(' '.join(names+ports))))
env=dict(symbols)
def get(k):return s.Integer(k) if isinstance(k,int) else env[k]
for name,op,a,b in d['source']:
    a,b=get(a),get(b)
    assert op in ['+','-','*']
    env[name]=a+b if op=='+' else a-b if op=='-' else a*b
rows=[s.expand(get(a)-get(b)) for a,b in d['comparisons']]
J,F,alpha,z,f,h,i,o,j,ss,w,tau,eta,zeta,y,gamma,N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta=[symbols[n] for n in names]
beta,K0,MC,MF=[symbols[n] for n in ports]
q=1+beta*J;k=eta+zeta;C=q-F-alpha;U=L+1;Y=a-E;Q=c-eta;T=P-k;H=4*a+3
expected=[U-q*q,N-q*U,X-w*q,Y-ss*N,E-X*Y,Q-k*Y,T-E*Q,tau*tau-P*T-1,D-X-a*c-gamma*H,Delta-a*a-H,C2-c*c,D*D-Delta*C2-1,k-1-c*j+V-h*E,c*j-V-((N-q)*(q-F)-L*C+(MC+q*MF)*J),(K0+w)*C-F-z*beta*J,F2-f*f,V-o*f+c,g-y*y+V*V,I-i*C2,Baux-I*I,Baux-Delta*(F2-1),y*y-Baux*g-1]
assert len(expected)==22
assert all(s.expand(u-v)==0 for u,v in zip(rows,expected))
shift=['F','alpha','z','h','i','j','s','w','eta','zeta','gamma','g']
sub={symbols[n]:symbols[n]+1 for n in shift}
shifted=[s.expand(r.subs(sub,simultaneous=True)) for r in rows]
published=json.loads((BASE/'source/selective12_source.json').read_text())
assert published['shifted_coordinates']==shift
terms=0;active=set()
for row,record in zip(shifted,published['rows']):
    po=s.Poly(row,*[symbols[n] for n in names]);assert str(po.as_expr())==record['polynomial']
    actual={}
    for powers,coefficient in po.terms():
        assert sum(powers)<=2
        factor=math.factorial(2-sum(powers))*math.prod(math.factorial(v) for v in powers)
        actual[powers]=(str(coefficient),str(s.expand(factor*coefficient)))
        active.add(powers);terms+=1
    given={tuple(t['alpha']):(t['coefficient'],t['weighted_coefficient']) for t in record['terms']}
    assert actual==given
assert terms==109 and len(active)==62
assert shifted[1].subs({symbols[n]:0 for n in names})==-1
layout_checks=[]
for path in sorted((BASE/'packing').glob('CERTIFICATE_*_selective12_*.json')):
    cert=json.loads(path.read_text())
    weights=cert['weights'];padding=cert['padding_exponent'];all_weights=[padding]+weights
    assert len(all_weights)==len(set(all_weights))==32
    assert min(all_weights)>=0
    targets=cert['target_exponents'];assert len(set(targets))==22
    target_lookup={v:k for k,v in enumerate(targets)}
    gamma=[]
    for l in range(32):
        for r in range(l,32):
            powers=[0]*31
            if l:powers[l-1]+=1
            if r:powers[r-1]+=1
            gamma.append((all_weights[l]+all_weights[r],tuple(powers)))
    assert len(gamma)==528
    reverse=[];hits=0;boundaries=[]
    for rownum,(poly,record) in enumerate(zip(shifted,cert['rows'])):
        sign=cert['coefficient_signs'][rownum];assert sign in [-1,1]
        terms=s.Poly(sign*poly,*[symbols[n] for n in names]).terms()
        expected_terms={a:c for a,c in terms}
        for term in record['terms']:
            alpha=tuple(term['alpha']);assert alpha in expected_terms
            coefficient=expected_terms[alpha]
            factor=math.factorial(2-sum(alpha))*math.prod(math.factorial(n) for n in alpha)
            assert term['coefficient']==str(coefficient)
            assert term['weighted_coefficient']==str(s.expand(factor*coefficient))
            exponent=(2-sum(alpha))*padding+sum(a*w for a,w in zip(alpha,weights))
            rev=targets[rownum]-exponent;assert rev>=0
            assert term['weight']==exponent and term['encoding_exponent']==rev
            reverse.append(rev);boundaries.append((rev,factor*coefficient))
            for other_exponent,other_alpha in gamma:
                k=target_lookup.get(rev+other_exponent)
                if k is not None:
                    assert k==rownum and other_alpha==alpha
                    hits+=1
    assert len(reverse)==len(set(reverse))==109 and hits==109
    dm=max(reverse);W=max(all_weights);Kcode=dm+2*W
    assert cert['Dmax']==dm and cert['maximum_weight']==W and cert['Kcode']==Kcode
    assert Kcode>=max(targets)+2
    leaders=[c for r,c in boundaries if r==dm]
    assert len(leaders)==1 and leaders[0].is_positive
    layout_checks.append({'path':str(path.relative_to(BASE)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'records':109,'possible_pair_interactions':109*528,'target_hits':hits,'W':W,'padding':padding,'Dmax':dm,'Kcode':Kcode,'headroom':Kcode-max(targets)})
zz,r0,r1,r2=s.symbols('Z r0 r1 r2')
def norm(z,a,b,c):
    q=z*z+c-a-b
    rr=q*q+4*z*z*c-4*a*b
    return rr*rr-16*z*z*c*q*q
product=s.Integer(1)
for e0 in [-1,1]:
    for e1 in [-1,1]:
        for e2 in [-1,1]:product*=zz+e0*r0+e1*r1+e2*r2
assert s.expand(product-norm(zz,r0*r0,r1*r1,r2*r2))==0
A,C,K,cap,g,ell,xx,yy,ee=s.symbols('A C K cap g ell xx yy ee')
delta=8*cap**3*g*K**2-g**2*(32*(C-K*ell)**2*cap**3+g**2*K**2)
assert s.expand(delta-(g*K**2*(8*cap**3-g**3)-32*g**2*cap**3*(C-K*ell)**2))==0
FF=4*(A*A-4)*ee*ee+1
GG=2*(A+2)*(A-2)**2*ee*ee-1
assert s.expand(GG-((A/2-1)*(FF-1)-1))==0
aa,pp=s.symbols('aa pp',integer=True)
rad1=((2*pp)**2-4)*K*K+4
radD=((2*aa)**2-4)*C*C+4
assert all(v%4==0 for v in s.Poly(rad1,pp,K).coeffs())
assert all(v%4==0 for v in s.Poly(radD,aa,C).coeffs())
native=BASE/'native'
native_ports={name:int.from_bytes(gzip.decompress((native/f'{name}.bin.gz').read_bytes()),'little') for name in ['beta','K','MC','MF_source']}
B=native_ports['beta']+1
assert B==1<<429959
assert native_ports['MC']%4==2 and (native_ports['MF_source']-B+1)%8==4
# The low-mask assertion forces C=1 mod4 for authentic repunit J=1 mod4.
assert [c for c in range(4) if ((c-1)%4)&3==0]==[1]
phase=[]
for Fmod in range(4):
    qmod,Jmod,Cmod=0,1,1
    Gmod=(qmod*(qmod-Fmod)-Cmod)%4
    Rmod=(Gmod*(qmod*qmod-1)+(native_ports['MC']+qmod*native_ports['MF_source'])*Jmod)%4
    assert Rmod==3
    phase.append(Rmod)
files=['integer/CONDITIONAL_SEPARATOR_PROOF.md','integer/SPARSE_SOURCE_PROOF.md','source/SELECTIVE_POSITIVITY_PROOF.md','native/INHERITED_SEPARATED_PROOF.md']
out={'status':'PASS','scope':'Exact local ring identities, source-data reconstruction and authentic native low-residue implication, plus separate ordinary proof review. No unbounded compiler/calibration theorem is claimed proved by execution.','source_sha256':hashlib.sha256(raw).hexdigest(),'source_row_identities':22,'affine_transformed_rows':22,'guarded_coordinates':shift,'coefficient_records':109,'active_monomials':len(active),'nonzero_source_row':2,'positional_certificates':layout_checks,'norm_factorization':'exact over Z[Z,r0,r1,r2]','delta_factorization':'exact','factored_G_identity':'exact','radicands_mod4':'exact polynomial coefficient divisibility','native_authentic_rank_phase':3,'phase_requires':'q=B^N, J=(q-1)/(B-1), native origin disjointness, MC=2 mod4','reviewed_files':[{'path':f,'sha256':hashlib.sha256((BASE/f).read_bytes()).hexdigest()} for f in files]}
(ROOT/'NEW_LOCAL_ADAPTER_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
