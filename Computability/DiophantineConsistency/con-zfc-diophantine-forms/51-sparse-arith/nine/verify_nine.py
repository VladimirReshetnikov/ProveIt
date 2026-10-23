#!/usr/bin/env python3
"""Independent literal-formula, exact-degree, and domain checks for nine variables."""
from pathlib import Path
from collections import Counter
import gzip,hashlib,json,math,random
ROOT=Path(__file__).resolve().parent
PARENT=ROOT.parent

def req(test,message):
    if not test:raise ValueError(message)

def recval(recipe,ports,p):
    return sum(t['coefficient']*math.prod(pow(x,e,p) for x,e in zip(ports,t['powers'])) for t in recipe)%p

def graph(obj,values,fixed,p):
    out=[]
    for k,n in enumerate(obj['nodes']):
        kind=n['kind']
        if kind=='variable':v=values[n['name']]
        elif kind=='literal':v=n['value']
        elif kind=='fixed':v=fixed[n['name']]
        else:
            req(0<=n['left']<k and 0<=n['right']<k,'Acyclic circuit')
            a,b=out[n['left']],out[n['right']]
            v=a+b if kind=='add' else a-b if kind=='sub' else a*b
        out.append(v%p)
    return out[obj['output']],{n:out[i] for n,i in obj['named_nodes'].items()}

def direct(obj,x,fixed,rows,targets,p):
    n=lambda a:a%p
    epsilon=x['epsilon']-1;g=x['g'];h=x['h'];s=x['s'];w=x['w'];phi=x['phi']-1;i=x['i'];j=x['j'];nn=x['n']-1
    b=n(fixed['base_floor']+epsilon);B=pow(b,3,p);weights=obj['weights'];W=max(weights);span=max(targets)+2*W
    ell=sum(pow(B,wi,p) for wi in weights)%p
    Dcode=0
    for row,E in zip(rows,targets):
        for alpha,co in row:Dcode+=co*pow(B,E-sum(a*wi for a,wi in zip(alpha,weights)),p)
    Dcode%=p;N0=pow(B,W+1,p);N1=n(4*pow(B,span+1,p));N=n(N0*N1)
    targetsum=sum(pow(B,E,p) for E in targets)%p
    mask=n(N0-1-(b-1)*ell);Tcode=n(mask+(B-2)*targetsum*N0)
    # Literal bounded sum, independent of the emitted divide-and-conquer graph.
    total=0;power=1
    for _ in range(span+1):total=n(total+power);power=n(power*B)
    Jcode=n(2*(1+g+ell)**2*Dcode+B*total);Scode=n(g+Jcode*N0)
    R=n((N-1)*((Scode+Tcode+1)*N+Tcode+1));cap=n(32*b*pow(B,W,p))
    U=n(N*N*w);Y=n(N*N*s);M=n(R*Y);P=n(2*M*M*U);K=n(R+1+h*(P-1));A=n(M*(U+1));B1=n(2*R+1);W1=n(b*w);C=n(B1+W1+phi);J=n(4*A-5);Q=n(3*W1*C-2*(W1*W1-1));D=n((A*A-1)*C*C+1);E=n(i*J*D*C*C);F=n((A*A-1)*E*E+1);G=n(A+F*(C*D+1-A));H=n(B1+j*C);I=n((G*G-1)*H*H+1)
    a0=n((P*P-1)*K*K+1);a1=n(D*F*I);u=n(J*F);v=n(Q*F+J*(H-C));m=n((K*K-4*(C-K*Y)**2)*cap-8*g*K*K)
    V0=n(P*K);V1=n(A*C*A*E*G*H);Mdiv=n(Q+H);Omega=n(u*m);E0=n(u*(nn+Mdiv)+v-2*Omega*Mdiv);Theta=n(E0-Omega*V0*V1)
    inner=n(Theta*Theta-Omega*Omega*(a0+V0*V0*a1));value=n(inner*inner-4*pow(Omega,4,p)*V0*V0*a0*a1)
    named=dict(b=b,B=B,Dcode=Dcode,ell=ell,N0=N0,N1=N1,N=N,mask=mask,targets=targetsum,Tcode=Tcode,Jcode=Jcode,Scode=Scode,R=R,Gcap=cap,U=U,Y=Y,M=M,P=P,K=K,A=A,C=C,J=J,Q=Q,D=D,E=E,F=F,G=G,H=H,I=I,a0=a0,a1=a1,u=u,v=v,m=m,V0=V0,V1=V1,Mdiv=Mdiv,Omega=Omega,E0=E0,Theta=Theta,inner=inner)
    return value,named

def degree(obj,fixed,p):
    ds=[];cs=[]
    for node in obj['nodes']:
        k=node['kind']
        if k=='variable':d,c=1,1
        elif k=='literal':d,c=0,node['value']%p
        elif k=='fixed':d,c=0,fixed[node['name']]
        else:
            a,b=node['left'],node['right']
            if k=='mul':d,c=ds[a]+ds[b],cs[a]*cs[b]%p
            else:
                d=max(ds[a],ds[b]);ca=cs[a] if ds[a]==d else 0;cb=cs[b] if ds[b]==d else 0
                c=(ca+cb if k=='add' else ca-cb)%p
        ds.append(d);cs.append(c)
    return ds[obj['output']],cs[obj['output']]

def norm_identity():
    # Sparse formal polynomials over Z in abstract x,y,z,D,F,I.
    dim=6;zero=(0,)*dim
    def c(k):return {zero:k} if k else {}
    def var(i):
        t=list(zero);t[i]=1;return {tuple(t):1}
    def add(a,b,sign=1):
        out=dict(a)
        for m,v in b.items():out[m]=out.get(m,0)+sign*v
        return {m:v for m,v in out.items() if v}
    def mul(a,b):
        out={}
        for m,v in a.items():
            for n,w in b.items():
                key=tuple(i+j for i,j in zip(m,n));out[key]=out.get(key,0)+v*w
        return {m:v for m,v in out.items() if v}
    x,y,z,D,F,I=[var(i) for i in range(dim)]
    # x=(AC)^2, y=(AE)^2,z=(GH)^2.
    lhs=add(mul(mul(x,y),z),mul(mul(D,F),I),-1)
    rhs=add(add(mul(mul(add(x,D,-1),y),z),mul(mul(D,add(y,F,-1)),z)),mul(mul(D,F),add(z,I,-1)))
    req(lhs==rhs,'Exact telescoping norm-product identity')

def main():
    objs={}
    for dom in ['positive','natural']:
        for suffix in ['', '_degree_certificate']:
            key=dom+suffix;obj=json.loads((ROOT/'generated'/f'multitarget_nine_{key}.json').read_text());objs[key]=obj
            counts=Counter(n['kind'] for n in obj['nodes'] if 'left' in n)
            req(dict(counts)==obj['operation_counts'] and sum(counts.values())==obj['total_operations'],'Operation ledger')
            live={obj['output']}
            for index in range(len(obj['nodes'])-1,-1,-1):
                req(index in live,'Dead graph node')
                node=obj['nodes'][index]
                if 'left'in node:live.update((node['left'],node['right']))
            req(len(obj['variables'])==9,'Nine variables')
    req(objs['positive']['total_operations']==682 and objs['natural']['total_operations']==685,'Main operation totals')
    ports=[int.from_bytes(gzip.decompress((PARENT/'coefficients/payloads'/f'{name}.bin.gz').read_bytes()),'little') for name in ['beta','K','MC','MF_source']]
    data=json.loads((PARENT/'data/coefficient_recipes.json').read_text());pack=json.loads((PARENT/'data/targets.json').read_text());targets=[None]*22
    for j,t in zip(pack['order'],pack['targets']):targets[j]=t
    rng=random.Random(20261023);cases=0;degreecert=[]
    for p in [1000000007,1000000009,998244353]:
        fixed={name:recval(recipe,ports,p) for name,recipe in data['recipes'].items()};fixed['base_floor']=pow(2,2134939,p)
        rows=[[(t['alpha'],t['sign']*(t['leaf'] if isinstance(t['leaf'],int) else fixed[t['leaf']])%p) for t in row] for row in data['rows']]
        valslist=[dict.fromkeys(objs['positive']['variables'],a) for a in [0,1,-1,2]]
        valslist += [{name:rng.randrange(-100,101) for name in objs['positive']['variables']} for _ in range(16)]
        for values in valslist:
            actual,named=graph(objs['positive'],values,fixed,p)
            expected,refs=direct(objs['positive'],values,fixed,rows,targets,p)
            req(actual==expected,'Literal nine-variable final equation')
            for name,value in named.items():req(refs[name]==value,'Named register '+name)
            cert,_=graph(objs['positive_degree_certificate'],values,fixed,p);req(actual==cert,'Cancellation-resolved evaluator')
            shifted={k:v-1 for k,v in values.items()};natural,_=graph(objs['natural'],shifted,fixed,p);req(actual==natural,'Positive/natural domain bijection')
            cases+=1
        dc,lc=degree(objs['positive_degree_certificate'],fixed,p)
        req(dc==33332620 and lc==pow(2,2050,p),'Exact total degree and diagonal leader')
        degreecert.append({'prime':p,'degree':dc,'leading_coefficient':lc,'expected_power_of_two':2050})
    norm_identity()
    # Materialize the additional fixed base floor; all other leaves were byte-checked by verify_source.
    val=1<<2134939;payload=val.to_bytes((val.bit_length()+7)//8,'little');path=PARENT/'coefficients/payloads/base_floor.bin.gz';path.write_bytes(gzip.compress(payload,mtime=0))
    manifest=json.loads((PARENT/'data/fixed_values.json').read_text());manifest.pop('beta_source')
    manifest['base_floor']={'sign':1,'bit_length':val.bit_length(),'uncompressed_bytes':len(payload),'sha256':hashlib.sha256(payload).hexdigest(),'file':'../coefficients/payloads/base_floor.bin.gz','encoding':'little-endian unsigned magnitude, separate sign'}
    for name,r in manifest.items():
        if name!='base_floor':r['file']='../'+r['file']
    (ROOT/'fixed_values.json').write_text(json.dumps(manifest,indent=2)+'\n')
    receipt={'status':'PASS','operations_positive':682,'operations_natural':685,'degree':33332620,
        'degree_certificates':degreecert,'literal_formula_cases':cases,'exact_telescoping_identity':True,
        'positive_natural_bijection_cases':cases,'cancellation_resolved_replays':cases,
        'all_nodes_live':True,'fixed_leaves':len(manifest),
        'scope':'Exact finite algebra and degree certificates plus finite implementation controls. No new proof-assistant certificate.'}
    (ROOT/'generated/VERIFICATION.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
