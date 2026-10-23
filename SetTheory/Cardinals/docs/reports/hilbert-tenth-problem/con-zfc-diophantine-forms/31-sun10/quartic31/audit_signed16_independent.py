#!/usr/bin/env python3
"""Independent data-only audit of the sixteen-integer circuit.

Does not import its emitter or circuit implementation.  The complete
58,905-position coefficient baseline is enumerated literally.
"""
import argparse, gzip, hashlib, itertools, json, random
from pathlib import Path

def require(c,m):
    if not c:raise ValueError(m)

def pow_sum(b,n,p):
    if n==0:return 1,0
    a,s=pow_sum(b,n//2,p)
    aa=a*a%p;ss=s*(1+a)%p
    return (aa*b%p,(ss+aa)%p) if n%2 else (aa,ss)

def run(sd):
    packet=json.loads((sd/'generated/signed16.json').read_text())
    data=json.loads((sd/'data/constants.json').read_text())
    binding=json.loads((sd/'data/coefficients_binding.json').read_text())
    instance=json.loads((sd/'data/INSTANCE.json').read_text())
    exponent=instance['z_index']['s']
    nu=data['nu'];L=5**(nu+1);pows=[5**i for i in range(nu+1)]
    exponents=[L-sum(pows[i] for i in iseq if i<=nu)
               for iseq in itertools.combinations_with_replacement(range(nu+2),4)]
    require(len(exponents)==58905 and len(set(exponents))==58905,'index support')
    ports={}
    for name,fn in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]:
        raw=gzip.decompress((sd/'data'/f'{fn}.bin.gz').read_bytes())
        record=next(r for r in binding['files'] if r['name']==fn)
        require(hashlib.sha256(raw).hexdigest()==record['sha256'],'coefficient byte hash')
        ports[name]=int.from_bytes(raw,'little')
    degree_records=[];modular_cases=0;named_checks=0
    rng=random.Random(3160)
    for p in [1000003,1000033]:
        z=pow(2,exponent,p);kap=pow(2,(exponent+1)*(L+1),p)
        fixed={'z_index':z,'kappa_index':kap}
        for row in data['coefficient_records']:
            total=0
            for term in row['coefficient_polynomial_in_fixed_ports']:
                x=term['coefficient']
                for name,power in zip(data['fixed_port_order'],term['powers']):x=x*pow(ports[name]%p,power,p)%p
                total=(total+x)%p
            fixed[row['name']]=total
        # Static degree upper bounds + actual-instance nonzero top diagonal.
        degrees=[];leaders=[]
        for n in packet['nodes']:
            k=n['kind']
            if k=='variable':d,c=1,1
            elif k=='literal':d,c=0,n['value']%p
            elif k=='fixed':d,c=0,fixed[n['name']]
            else:
                a,b=n['left'],n['right']
                if k=='mul':d,c=degrees[a]+degrees[b],leaders[a]*leaders[b]%p
                else:
                    d=max(degrees[a],degrees[b]);c=((leaders[a] if degrees[a]==d else 0)+(1 if k=='add' else -1)*(leaders[b] if degrees[b]==d else 0))%p
            degrees.append(d);leaders.append(c)
        out=packet['output']
        require(degrees[out]==813056*L+10016 and leaders[out]!=0,'exact-degree certificate')
        degree_records.append(dict(prime=p,degree=degrees[out],top_diagonal_coefficient=leaders[out]))
        for case in range(3):
            v={x:rng.randrange(-4,5) for x in packet['variables']}
            if case==0:v['t']=0
            else:v['t']=case
            vals=[]
            for n in packet['nodes']:
                k=n['kind']
                if k=='variable':val=v[n['name']]
                elif k=='fixed':val=fixed[n['name']]
                elif k=='literal':val=n['value']
                else:
                    a,b=vals[n['left']],vals[n['right']]
                    val=a+b if k=='add' else a-b if k=='sub' else a*b
                vals.append(val%p)
            # Literal mathematical definition, independent of DAG and Horner code.
            b=kap*v['t']**2%p;B=pow(b,5,p);q=pow(B,L,p)
            ell=sum(pow(B,5**r,p) for r in range(1,nu+1))%p
            lam=pow_sum(B,4*L,p)[1]
            e=(z*sum(pow(B,r,p) for r in exponents)+sum(fixed[r['name']]*pow(B,L-r['expo'],p) for r in data['coefficient_records']))%p
            N=pow(q,16,p);Gc=32*b*pow(B,5**nu,p)%p
            g,h,s,w,i,j=[v[x]+1 for x in ['g0','h0','s0','w0','i0','j0']]
            R=((g+e*q**3+ell*q**5+(2*(e-z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7)*(N*N-N)+(q**3-b*ell+ell+(B-2*z)*lam*q**3+(B-2)*q**8)*(N*N-1))%p
            U=N*N*w%p;Y=N*N*s%p;M=R*Y%p;P=2*M*M*U%p
            K=(R+1+h*(P-1))%p;A=M*(U+1)%p;Bprime=2*R+1;Wsmall=b*w%p
            C=(Bprime+Wsmall+v['phi'])%p;J=(4*A-5)%p;Q=(3*Wsmall*C-2*(Wsmall*Wsmall-1))%p
            D=((A*A-1)*C*C+1)%p;E=i*J*D*C*C%p;F=((A*A-1)*E*E+1)%p
            Gp=(A+F*(C*D+1-A))%p;H=(Bprime+j*C)%p;I=((Gp*Gp-1)*H*H+1)%p
            a0=((P*P-1)*K*K+1)%p;a1=D*F*I%p;margin=(K*K*Gc-4*(C-K*Y)**2*Gc-8*g*K*K)%p
            stack=1;guards={}
            for num,name in enumerate(['g0','s0','w0','phi','j0'],1):
                stack=stack*(1+4*(3*v[name]+2)*stack*stack*v['z'+str(num)]**2)%p;guards['guard'+str(num)]=stack
            stack=stack*(1+4*(3*margin-1)*stack*stack*v['z6']**2)%p;guards['guard6']=stack
            DD=J*F%p;TT=(Q*F+J*(H-C))%p
            Z=v['i0']+1
            for num in range(1,7):Z=Z*v['z'+str(num)]%p
            S=Z*pow(DD,5,p)%p;r=(TT+DD*v['v'])%p
            T=((r**3-DD*DD*r-DD**3)*(r*r+23*DD*DD))%p
            V0=(P*P+K*K+2)%p;w1=stack;w2=stack*V0%p
            X=(S*v['u']-T)%p;A0=S*S*stack%p;A1=S*S*w1*w1*a0%p;A2=S*S*w2*w2*a1%p
            V=(X*X+A2-A0-A1)%p;W=(V*V+4*X*X*A2-4*A0*A1)%p
            out2=(W*W-16*V*V*X*X*A2)%p
            named=dict(b=b,B=B,q=q,ell=ell,**{'lambda':lam},e=e,N=N,Gcap=Gc,R=R,U=U,Y=Y,M=M,P=P,K=K,A=A,Wsmall=Wsmall,C=C,J=J,Q=Q,D=D,E=E,F=F,Gp=Gp,H=H,I=I,a0=a0,a1=a1,margin=margin,Ddiv=DD,Tdiv=TT,Znonzero=Z,Smerge=S,Tmerge=T,weight1=w1,weight2=w2,V0=V0,Xnorm=X,A0norm=A0,A1norm=A1,A2norm=A2,Vnorm=V,Wnorm=W,F16=out2,**guards)
            for name,val in named.items():
                if name not in packet['named_nodes']:
                    require(name=='weight2','unexpected pruned named node '+name)
                    continue
                require(vals[packet['named_nodes'][name]]==val%p,'named-node mismatch '+name);named_checks+=1
            require(vals[out]==out2,'complete direct formula mismatch');modular_cases+=1
    # Exact independent product in Z[r0,r1,r2]/(rj^2-aj).
    def mult(x,y,rad):
        out=[0]*8
        for i,a in enumerate(x):
            for j,b in enumerate(y):
                coef=a*b
                for k in range(3):
                    if (i&j)&(1<<k):coef*=rad[k]
                out[i^j]+=coef
        return out
    for _ in range(100):
        rad=[rng.randrange(-6,7) for _ in range(3)];S=rng.randrange(-5,6);X=rng.randrange(-5,6);w1=rng.randrange(-5,6);w2=rng.randrange(-5,6)
        result=[1]+[0]*7
        for eps in itertools.product([-1,1],repeat=3):
            factor=[0]*8;factor[0]=X
            for j,wgt in enumerate([1,w1,w2]):factor[1<<j]=-S*eps[j]*wgt
            result=mult(result,factor,rad)
        A0=S*S*rad[0];A1=S*S*w1*w1*rad[1];A2=S*S*w2*w2*rad[2]
        V=X*X+A2-A0-A1;W=V*V+4*X*X*A2-4*A0*A1
        require(result==[W*W-16*V*V*X*X*A2]+[0]*7,'eight-factor norm identity')
    report=dict(status='PASS',source='independent formula transcription; no generator imports',variable_count=len(packet['variables']),operations=sum(n['kind'] in ['add','sub','mul'] for n in packet['nodes']),full_index_positions=len(exponents),actual_coefficient_hashes_checked=True,modular_cases=modular_cases,named_node_checks=named_checks,exact_norm_ring_tests=100,degree_certificates=degree_records,scope='Finite transcription and algebra checks; the proof of consistency equivalence is a separate mathematical argument.')
    outpath=Path(__file__).with_name('SIGNED16_LITERAL_AUDIT.json');outpath.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--signed-dir',type=Path,default=Path(__file__).resolve().parent.parent/'signed16');a=p.parse_args();run(a.signed_dir)
