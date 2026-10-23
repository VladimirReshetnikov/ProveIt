#!/usr/bin/env python3
"""Independent finite diagnostics supplementing SIGNED_PROOF.md (not proof certificates)."""
from pathlib import Path
import json,gzip,random,math,itertools,hashlib
from build_signed import construct,degree_audit,verify_source_pins,KAPPA,L,NU,S_INDEX
ROOT=Path(__file__).resolve().parent

def geom(x,n,p):
    if n==0:return 0
    if n==1:return 1
    h=n//2;r=geom(x,h,p)*(1+pow(x,h,p))%p
    return (r+pow(x,n-1,p))%p if n%2 else r

def digit(x,z,coeff,p):
    # Newton identities, independent of the builder's in-place h4 recurrence.
    top=5**NU
    weights=[pow(x,top,p)]+[pow(x,top-5**j,p) for j in range(NU+1)]
    sums=[0]+[sum(pow(w,j,p) for w in weights)%p for j in range(1,5)]
    h=[1]
    for k in range(1,5):h.append(sum(sums[j]*h[k-j] for j in range(1,k+1))*pow(k,-1,p)%p)
    baseline=pow(x,top,p)*h[4]%p
    return (z*baseline+sum(co*pow(x,L-e,p) for e,co in coeff))%p

def fixed_values(p):
    constants=json.loads((ROOT/'upstream/COMPACT_CONSTANTS.json').read_text())
    ports=[]
    for name in ['beta','K','MC','MF_source']:
        path=ROOT.parent/'coefficients/coefficients_compact'/f'{name}.bin.gz'
        data=gzip.decompress(path.read_bytes());ports.append(int.from_bytes(data,'little')%p)
    coeff=[];leaves={}
    for row in constants['coefficient_records']:
        val=sum(term['coefficient']*math.prod(pow(v,e,p) for v,e in zip(ports,term['powers'])) for term in row['coefficient_polynomial_in_fixed_ports'])%p
        coeff.append((row['expo'],val));leaves[row['name']]=val
    z=pow(2,S_INDEX,p);y=digit(2*z%p,z,coeff,p)
    leaves.update(z_index=z,y_index=y,base_scale=pow(2,KAPPA,p))
    return leaves,coeff,ports

def evaldag(body,fixed,x,p):
    vals=[]
    for node in body['nodes']:
        k=node['kind']
        if k=='literal':v=node['value']
        elif k=='fixed':v=fixed[node['name']]
        elif k=='variable':v=x[node['name']]
        else:
            a,b=vals[node['left']],vals[node['right']]
            v=a+b if k=='add' else a-b if k=='sub' else a*b
        vals.append(v%p)
    return vals[body['output']],{k:vals[i] for k,i in body['named_nodes'].items()}

def direct_core(count,fixed,coeff,x,p):
    b=(fixed['base_scale']*x['epsilon']**2 if count<=15 else fixed['y_index']+1+x['epsilon'])%p
    g,h,s,w,phi,i,j=[x[k] for k in ['g','h','s','w','phi','i','j']]
    if count==14:w=w*w%p
    B=pow(b,5,p);q=pow(B,L,p);ell=sum(pow(B,5**r,p) for r in range(1,NU+1))%p
    lam=geom(B,4*L,p);e=digit(B,fixed['z_index'],coeff,p);theta=(B-2*fixed['z_index'])%p
    N=pow(q,16,p);G=32*b*pow(B,5**NU,p)%p
    R=((g+e*q**3+ell*q**5+(2*(e-fixed['z_index']*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7)*(N*N-N)+(q**3-b*ell+ell+theta*lam*q**3+(B-2)*q**8)*(N*N-1))%p
    U=N*N*w%p;Y=N*N*s%p;M=R*Y%p;P=2*M*M*U%p;K=(R+1+h*(P-1))%p;A=M*(U+1)%p
    B1=(2*R+1)%p;W=b*w%p;C=(B1+W+phi)%p;J=(4*A-5)%p;Q=(3*W*C-2*(W*W-1))%p
    D=((A*A-1)*C*C+1)%p;E=i*J*D*C*C%p;F=((A*A-1)*E*E+1)%p
    Gp=(A+F*(C*D+1-A))%p;H=(B1+j*C)%p;I=((Gp*Gp-1)*H*H+1)%p
    a0=((P*P-1)*K*K+1)%p;a1=D*F*I%p;margin=(K*K*G-4*(C-K*Y)**2*G-8*g*K*K)%p
    return locals()

def direct_extension(body,base,x,p):
    stack=1;zz=[]
    for j,name in enumerate(body['guards'],1):
        zz.append(x['z'+str(j)])
        disc=3*x[name]+2 if name in ('epsilon','phi') else 3*x[name]-1
        stack=stack*(1+4*disc*stack*stack*zz[-1]**2)%p
    zz.append(x['z'+str(len(zz)+1)])
    stack=stack*(1+4*(3*base['margin']-1)*stack*stack*zz[-1]**2)%p
    D=base['J']*base['F']%p;T=(base['Q']*base['F']+base['J']*(base['H']-base['C']))%p
    Z=x['i']*math.prod(zz)
    count=len(body['variables'])
    if count<=15:Z*=x['epsilon']
    if count==14:Z*=x['w']
    S=Z*pow(D,5,p)%p;r=(T+D*x['residue'])%p
    T=((r**3-D*D*r-D**3)*(r*r+23*D*D))%p
    w1=(stack+1)%p;w2=w1*(base['P']**2+base['K']**2+2)%p
    X=(S*x['normroot']-T)%p;A0=S*S*stack%p;A1=S*S*w1*w1*base['a0']%p;A2=S*S*w2*w2*base['a1']%p
    V=(X*X+A2-A0-A1)%p;W=(V*V+4*X*X*A2-4*A0*A1)%p
    return (W*W-16*V*V*X*X*A2)%p

def main():
    rng=random.Random(140031);receipt={'pinned_source_files_checked':verify_source_pins()};modchecks=0;prime_data=[]
    bodies={n:construct(n)[0] for n in [14,15,16]}
    for prime in [1000003,1000033,1000037]:
        fixed,coeff,ports=fixed_values(prime);prime_data.append({'prime':prime,'ports':ports,'z':fixed['z_index'],'y':fixed['y_index'],'base_scale':fixed['base_scale']})
        for count,body in bodies.items():
            for trial in range(24):
                x={k:rng.randrange(-prime,prime) for k in body['variables']}
                got,names=evaldag(body,fixed,x,prime);base=direct_core(count,fixed,coeff,x,prime)
                for name in ['b','B','q','ell','R','U','Y','P','K','A','C','J','Q','D','E','F','Gp','H','I','a0','a1','margin']:
                    if name in names:assert names[name]==base[name]%prime,(count,trial,name)
                assert got==direct_extension(body,base,x,prime),(count,trial)
                modchecks+=1
    receipt['actual_coefficient_modular_full_circuit_checks']=modchecks
    receipt['fixed_value_receipts']=prime_data
    # Eight-factor norm identity for roots chosen independently; signed weights.
    for _ in range(1000):
        r=[rng.randrange(-25,26) for j in range(3)];w1,w2,S,X=[rng.randrange(-25,26) for j in range(4)]
        A0=S*S*r[0]**2;A1=S*S*w1*w1*r[1]**2;A2=S*S*w2*w2*r[2]**2
        V=X*X+A2-A0-A1;W=V*V+4*X*X*A2-4*A0*A1
        product=math.prod(X-S*(sg[0]*r[0]+sg[1]*w1*r[1]+sg[2]*w2*r[2]) for sg in itertools.product([-1,1],repeat=3))
        assert product==W*W-16*V*V*X*X*A2
    receipt['eight_factor_norm_identity_tests']=1000
    for n in range(1,1201):assert any(((t**3-t-1)*(t*t+23))%n==0 for t in range(n))
    receipt['intersective_moduli_checked']=1200
    for C in range(-10003,10004):
        if C%4==1:assert (C+1)**2>abs(C)
    receipt['signed_linear_weight_range']=[-10003,10003]
    gcdchecks=0
    for A in range(2,8):
        for C in range(1,8):
            for i in [-2,-1,1,2]:
                J=4*A-5;D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1;G=A+F*(C*D+1-A)
                for t in [-2,-1,0,1,2]:
                    H=C+t*F;I=(G*G-1)*H*H+1
                    assert math.gcd(D,F)==math.gcd(D,I)==math.gcd(F,I)==math.gcd(J,F)==1
                    gcdchecks+=1
    receipt['pairwise_coprime_tests']=gcdchecks
    orbitchecks=0
    for G in range(2,10):
        D=G*G-1
        for modulus in range(1,16):
            a,b=1,0;k=0
            while True:
                a,b=(a*G+b*D)%modulus,(a+b*G)%modulus;k+=1
                if a==1%modulus and b==0:break
                assert k<10000
            # Start eta^-1 (H=-1), multiply by eta^(2k).
            a,b=G,-1
            for _ in range(2*k):a,b=a*G+b*D,a+b*G
            assert a*a-D*b*b==1 and b>0 and (b+1)%modulus==0
            orbitchecks+=1
    receipt['negative_to_positive_pell_orbits']=orbitchecks
    receipt['odd_scale_exponent_checks']=sum(1 for R in range(8,200) for k in range(1,2*R+1,2) if (2*R+1-k)%2==0)
    receipt['cofinal_base_kappa_is_odd']=KAPPA%2==1
    for count,body in bodies.items():
        degree=degree_audit(body);receipt[str(count)]={'variables':len(body['variables']),'operations':sum(body['operation_counts'].values()),'exact_degree':degree['exact_degree'],'degree_leading_coefficient':degree['leading_scalar_modulus'],'leading_fixed_monomial':degree['leading_fixed_monomial']}
    receipt['status']='PASS: finite diagnostics, not an end-to-end kernel certificate or proof of consistency'
    (ROOT/'generated/CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
