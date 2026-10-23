#!/usr/bin/env python3
"""Independent finite audits of the explicit equation; not a halting search.

Exact source coefficient reconstruction, index bound, payload hashes, ordinary
norm polynomial identity, full digit sum, modular literal/DAG agreement, and
degree attainment are checked. The report supplies the universal proof.
"""
from pathlib import Path
from collections import defaultdict
from itertools import product,combinations_with_replacement
from math import factorial,comb,isqrt,gcd
import gzip,hashlib,json,random
from build_signed16 import construct,GUARDS
from circuit import evaluate

ROOT=Path(__file__).resolve().parent

def sparse_add(a,b):
    out=a.copy()
    for e,c in b.items():
        out[e]=out.get(e,0)+c
        if out[e]==0:del out[e]
    return out
def sparse_mul(a,b):
    out={}
    for e,c in a.items():
        for f,d in b.items():
            k=tuple(x+y for x,y in zip(e,f));out[k]=out.get(k,0)+c*d
    return {k:v for k,v in out.items() if v}

def verify_coefficients():
    parent=json.loads((ROOT/'data/parent_quartic31.json').read_text())
    const=json.loads((ROOT/'data/constants.json').read_text())
    n=len(parent['variables']); whole={}
    for eq in parent['equations']:
        shifted={}
        for row in eq['terms']:
            powers=row['powers']; options=[range(powers[j]+1) for j in range(n)]
            for ex in product(*options):
                c=row['coefficient']
                for j in range(n):c*=comb(powers[j],ex[j])
                k=tuple(ex)+tuple(powers[n:]);shifted[k]=shifted.get(k,0)+c
        shifted={k:v for k,v in shifted.items() if v}
        whole=sparse_add(whole,sparse_mul(shifted,shifted))
    rec={}
    for ex,c in whole.items():
        alpha=(0,)+ex[:n]; weight=factorial(4-sum(alpha))
        for e in alpha:weight*=factorial(e)
        rec.setdefault(alpha,{})[ex[n:]]=c*weight
    received={tuple(r['alpha']):{tuple(v['powers']):v['coefficient'] for v in r['coefficient_polynomial_in_fixed_ports']}
              for r in const['coefficient_records']}
    assert rec==received, 'Weighted index coefficients differ from literal parent'
    assert len(rec)==402 and max(sum(ex[:n]) for ex in whole)==4
    # Parent normalization: all positive coordinates 1 give residual E-X(a-E)=1.
    assert parent['equations'][4]['equation']=='E = X(a-E)'
    return const,{'weighted_records':len(rec),'shifted_symbolic_terms':len(whole),'exact_reconstruction':True}

def ports_and_index(const):
    binding=json.loads((ROOT/'data/coefficients_binding.json').read_text()); ports={}; rows=[]
    for row in binding['files']:
        name=row['name']; gz=(ROOT/'data'/f'{name}.bin.gz').read_bytes(); raw=gzip.decompress(gz)
        assert hashlib.sha256(raw).hexdigest()==row['sha256']
        assert hashlib.sha256(gz).hexdigest()==row['gzip_sha256']
        value=int.from_bytes(raw,'little');assert value.bit_length()==row['bit_length']
        ports[{'K':'K0','MF_source':'MF'}.get(name,name)]=value
        rows.append({'name':name,'bytes':len(raw),'bits':value.bit_length(),'sha256':row['sha256']})
    bnd=json.loads((ROOT/'data/index_bound.json').read_text()); s=bnd['index_exponent']; z=1<<s
    bits=[ports[x].bit_length() for x in const['fixed_port_order']]
    assert bits==bnd['port_bit_lengths']
    for row in const['coefficient_records']:
        upper=sum(abs(t['coefficient']) << sum(e*b for e,b in zip(t['powers'],bits))
                  for t in row['coefficient_polynomial_in_fixed_ports'])
        assert upper+1<z
    return ports,s,{'payloads':rows,'z_exponent':s,'strict_bounds_checked':len(const['coefficient_records']),
                   'kappa_exponent':(s+1)*(const['L']+1)}

def leaves(const,ports,s,p):
    result={'z_index':pow(2,s,p),'kappa_index':pow(2,(s+1)*(const['L']+1),p)}
    for row in const['coefficient_records']:
        total=0
        for t in row['coefficient_polynomial_in_fixed_ports']:
            v=t['coefficient']
            for name,e in zip(const['fixed_port_order'],t['powers']):v=v*pow(ports[name]%p,e,p)%p
            total+=v
        result[row['name']]=total%p
    return result

def digit_value(B,z,const,fixed,p):
    """Literal complete sum, including EVERY zero-weight coefficient position."""
    nu=const['nu'];L=const['L']; powers=[5**j for j in range(nu+1)]
    total=0; count=0
    for size in range(5):
        for js in combinations_with_replacement(range(nu+1),size):
            expo=sum(powers[j] for j in js)
            total=(total+z*pow(B,L-expo,p))%p;count+=1
    for row in const['coefficient_records']:
        total=(total+fixed[row['name']]*pow(B,L-row['expo'],p))%p
    assert count==comb(nu+5,4)
    return total,count

def literal(x,fixed,const,p,digit=None):
    """Independent scalar transcription, not evaluated by walking the DAG."""
    def red(v):return v%p
    nu=const['nu']; L=const['L']; z=fixed['z_index']; b=red(fixed['kappa_index']*x['t']**2)
    B=pow(b,5,p);q=pow(B,L,p);ell=sum(pow(B,5**j,p) for j in range(1,nu+1))%p
    def geometric(base,n):
        if n==0:return 0
        if n==1:return 1
        h=n//2;r=geometric(base,h);power=pow(base,h,p)
        return (r*(1+power)+(power*power if n%2 else 0))%p
    lam=geometric(B,4*L)
    e=digit if digit is not None else digit_value(B,z,const,fixed,p)[0]
    N=pow(q,16,p);cap=red(32*b*pow(B,5**nu,p))
    g,h,s,w,i,j=[x[k]+1 for k in ['g0','h0','s0','w0','i0','j0']]
    R=red((g+e*q**3+ell*q**5+(2*(e-z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7)*(N*N-N)
          +(q**3-b*ell+ell+(B-2*z)*lam*q**3+(B-2)*q**8)*(N*N-1))
    U=red(N*N*w);Y=red(N*N*s);MM=red(R*Y);P=red(2*MM*MM*U)
    K=red(R+1+h*(P-1)); A=red(MM*(U+1));bp=red(2*R+1);W=red(b*w)
    C=red(bp+W+x['phi']);J=red(4*A-5);Q=red(3*W*C-2*(W*W-1))
    D=red((A*A-1)*C*C+1);E=red(i*J*D*C*C);F=red((A*A-1)*E*E+1)
    Gp=red(A+F*(C*D+1-A));H=red(bp+j*C);I=red((Gp*Gp-1)*H*H+1)
    a0=red((P*P-1)*K*K+1);a1=red(D*F*I);m=red(K*K*cap-4*(C-K*Y)**2*cap-8*g*K*K)
    stack=1
    for n,key in enumerate(GUARDS,1):stack=red(stack*(1+4*(3*x[key]+2)*stack*stack*x['z'+str(n)]**2))
    stack=red(stack*(1+4*(3*m-1)*stack*stack*x['z6']**2))
    d=red(J*F);t=red(Q*F+J*(H-C));nz=i
    for k in range(1,7):nz=red(nz*x['z'+str(k)])
    S=red(nz*pow(d,5,p));r=red(t+d*x['v']);T=red((r**3-d*d*r-d**3)*(r*r+23*d*d))
    V0=red(P*P+K*K+2);X=red(S*x['u']-T)
    A0=red(S*S*stack);A1=red(S*S*stack*stack*a0);A2=red(S*S*stack*stack*V0*V0*a1)
    V=red(X*X+A2-A0-A1);Wn=red(V*V+4*X*X*A2-4*A0*A1)
    out=red(Wn*Wn-16*V*V*X*X*A2)
    return out,{'b':b,'B':B,'q':q,'ell':ell,'lambda':lam,'e':e,'R':R,'a0':a0,'a1':a1,
                'margin':m,'guard6':stack,'Ddiv':d,'Tdiv':t,'Smerge':S,'Tmerge':T,'F16':out}

def degree_certificate(body,fixed,p):
    h=[]
    for n in body['nodes']:
        k=n['kind']
        if k=='literal':q=(0,n['value']%p)
        elif k=='fixed':q=(0,fixed[n['name']])
        elif k=='variable':q=(1,1)
        else:
            a,b=h[n['left']],h[n['right']]
            if k=='mul':q=(a[0]+b[0],a[1]*b[1]%p)
            else:
                degree=max(a[0],b[0]);sign=1 if k=='add' else -1
                q=(degree,((a[1] if a[0]==degree else 0)+sign*(b[1] if b[0]==degree else 0))%p)
        h.append(q)
    deg,lc=h[body['output']]
    assert deg==body['exact_degree'] and lc!=0
    selected=['R','P','K','A','D','E','F','Gp','H','I','a0','a1','Ddiv','margin','guard5','guard6','Smerge','Tmerge','Xnorm','A0norm','A1norm','A2norm','F16']
    return {'degree':deg,'prime':p,'attaining_diagonal_leading_coefficient_mod_prime':lc,
            'named_degrees':{k:h[body['named_nodes'][k]][0] for k in selected}}

def norm_identity():
    # Exact formal identity in four indeterminates X,r0,r1,r2.
    def variable(j):e=[0]*4;e[j]=1;return {tuple(e):1}
    def scale(a,k):return {e:v*k for e,v in a.items()}
    X,r0,r1,r2=[variable(j) for j in range(4)]
    X2=sparse_mul(X,X); A=[sparse_mul(r,r) for r in [r0,r1,r2]]
    V=sparse_add(sparse_add(X2,A[2]),scale(sparse_add(A[0],A[1]),-1))
    W=sparse_add(sparse_add(sparse_mul(V,V),scale(sparse_mul(X2,A[2]),4)),scale(sparse_mul(A[0],A[1]),-4))
    out=sparse_add(sparse_mul(W,W),scale(sparse_mul(sparse_mul(V,V),sparse_mul(X2,A[2])),-16))
    prod={(0,0,0,0):1}
    for signs in product([-1,1],repeat=3):
        f=X.copy()
        for r,s in zip([r0,r1,r2],signs):f=sparse_add(f,scale(r,-s))
        prod=sparse_mul(prod,f)
    assert out==prod
    return {'exact_polynomial_identity':True,'terms':len(out)}

def run():
    body,aliases=construct();const,coefcheck=verify_coefficients();ports,s,indexcheck=ports_and_index(const)
    rng=random.Random(1620261022); modular=[];named_comparisons=0;degrees=[]
    for p in [101,1009,1000003]:
        fixed=leaves(const,ports,s,p);degrees.append(degree_certificate(body,fixed,p))
        # One complete 58,905-position digit-sum check per prime; reuse its
        # b while varying the seven independent Jones coordinates and guards.
        t=rng.randrange(1,p);B=pow(fixed['kappa_index']*t*t%p,5,p)
        digit,count=digit_value(B,fixed['z_index'],const,fixed,p)
        for rep in range(12):
            x={k:rng.randrange(-11,12) for k in body['variables']};x['t']=t
            val,named=evaluate(body,fixed,x,p);direct,other=literal(x,fixed,const,p,digit)
            assert val==direct
            for k,v in other.items():assert named[k]==v;named_comparisons+=1
        modular.append({'prime':p,'full_digit_positions':count,'full_circuit_assignments':12,
                        'kappa_residue':fixed['kappa_index'],'z_residue':fixed['z_index']})
    # Finite negative/boundary controls for the new signed weights.
    weights=0
    for C in range(-101,102):
        if C%4!=1 or abs(C)<=1:continue
        for P in range(-6,7):
            for K in range(-6,7):
                a0=(P*P-1)*K*K+1;V0=P*P+K*K+2
                assert (V0-1)**2>=abs(a0)
                assert C*C>abs(C)
                # Rational upper bound: sqrt|C|<|C| and sqrt|a0|<=V0-1.
                assert abs(C)*V0>0
                weights+=1
    norm=norm_identity()
    report={'status':'PASS','scope':'Finite exact arithmetic/circuit audits; universal semantic proof is in report.tex.',
            'variables':len(body['variables']),'operations':body['operation_counts'],
            'total_operations':sum(body['operation_counts'].values()),'exact_degree':body['exact_degree'],
            'coefficient_reconstruction':coefcheck,'index_and_payloads':indexcheck,
            'literal_modular_checks':modular,'named_node_comparisons':named_comparisons,
            'degree_certificates':degrees,'norm_identity':norm,'weight_boundary_cases':weights}
    (ROOT/'generated').mkdir(exist_ok=True)
    (ROOT/'generated/VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['degree_certificates','index_and_payloads']},indent=2))
    return report
if __name__=='__main__':run()
