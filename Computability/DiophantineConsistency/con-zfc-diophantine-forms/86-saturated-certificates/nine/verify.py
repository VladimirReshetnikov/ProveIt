#!/usr/bin/env python3
"""Sealed data, exact source extraction, exact majorant and literal-DAG audits.

Finite checks certify these data/algebra facts, not ZFC consistency.
"""
from pathlib import Path
from collections import Counter
import gzip, hashlib, importlib.util, json, math, random
from circuit import evaluate
from build import build
from verify_majorant import audit as audit_majorant
from poly import value

ROOT=Path(__file__).resolve().parent
def require(p,msg):
    if not p:raise ValueError(msg)
def read(p):return json.loads(p.read_text())
def fixed(profile):
    base=ROOT/'baseline/compact2082' if profile=='compact2082' else ROOT
    rel='fixed/BINDING.json' if profile=='compact2082' else 'fixed/h1868/BINDING.json'
    vals={}
    for r in read(base/rel)['records']:
        blob=(base/r['path']).read_bytes();raw=gzip.decompress(blob)
        require(hashlib.sha256(blob).hexdigest()==r['gzip_sha256'],'fixed gzip hash')
        require(hashlib.sha256(raw).hexdigest()==r['raw_sha256'],'fixed integer hash')
        vals[r['name']]=r['sign']*int.from_bytes(raw,'little')
    return vals

def extraction():
    spec=importlib.util.spec_from_file_location('retained_extraction',ROOT/'baseline/h1868/check.py')
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
    code=read(ROOT/'data/code.json');source=read(ROOT/'data/source.json');kern=read(ROOT/'data/kernels.json')
    c,k=mod.construct(source,code['weights'],code['targets_by_row'],code['row_orientations'])
    require(json.loads(json.dumps(c))==code and k==kern,'all source/kernel identities')
    return dict(identities=22,exhaustive_interactions=c['exhaustive_interactions'],height=c['convolution_height'])

def source_direct(v,ports,p):
    b,g,h,s,w,C,i,j,n=[v[k]%p for k in ['b','g','h','s','w','C','i','j','n']]
    B=pow(2,2134939,p)*b*b%p
    code=read(ROOT/'data/code.json');kern=read(ROOT/'data/kernels.json')
    ell=sum(pow(B,e,p) for e in code['weights'])%p
    targets=sum(pow(B,e,p) for e in code['targets_by_row'])%p
    ds=[]
    for layer in kern['kernels']:
        out=0
        for t in layer['terms']:
            coefficient=sum(z['coefficient']*math.prod(pow(x,e,p) for x,e in zip(ports,z['powers'])) for z in t['coefficient'])%p
            out=(out+coefficient*pow(B,t['exponent'],p))%p
        ds.append(out)
    N0=pow(B,117,p);Us=(ell+g)%p;Gsrc=((ds[2]*Us+ds[1])*Us+ds[0])%p
    mask=(N0-1-(b-1)*ell)%p
    Tc=(mask+(B-2)*targets*N0)%p
    Sc=(g+N0*(2*Gsrc+targets))%p
    L=2*b*pow(B,1986,p)%p
    N=pow(2,16012032,p)*pow(B,1055,p)%p
    R=(L*(Sc+Tc+1)-Sc-1)%p
    U=N*N*w%p;Y=N*N*s%p;M=R*Y%p
    P=2*M*M*U%p;K=(R+1+h*(P-1))%p
    A=M*(U+1)%p;B1=(2*R+1)%p;W1=b*w%p;J=(4*A-5)%p
    Q=(3*W1*C-2*(W1*W1-1))%p;cap=b*pow(B,116,p)%p
    margin=(K*K*(4*cap-g)-16*cap*(C-K*Y)**2)%p
    Omega=J*margin%p;E0=(J*(n+W1*W1)+Q)%p
    V0=P*K%p;a0=((P*P-1)*K*K+1)%p
    return dict(B=B,R=R,N=N,A=A,B1=B1,J=J,C=C,K=K,P=P,U=U,Y=Y,
                margin=margin,Omega=Omega,E0=E0,V0=V0,a0=a0)

def tail_direct(reg,v,p,kind):
    A,C,J=reg['A'],reg['C'],reg['J'];i=v['i']%p
    D=((A*A-1)*C*C+1)%p;r=i*J*C*C%p
    F=((A*A-1)*D*r*r+1)%p
    G=(A+F*(C*D+1-A))%p;Z=(reg['B1']+(v['j']-1)*C)%p
    H=(C+F*Z)%p;I=((G*G-1)*H*H+1)%p
    a1=D*F*I%p
    if kind=='simple':V1=A*r*D*G*H%p
    else:
        poly={tuple(t['powers']):t['coefficient'] for t in read(ROOT/'data/saturated_corrected_P.json')['terms']}
        V1=value(poly,(A,C,i,Z),p);a1=a1*(1024*pow(C,5,p)*i)**2%p
    om=reg['Omega'];theta=(reg['E0']-om*(reg['V0']+V1))%p
    out=((theta*theta-om*om*(reg['a0']+a1))**2-4*om**4*reg['a0']*a1)%p
    return out,dict(D=D,F=F,G=G,H=H,I=I,V1=V1,a1=a1,Z=Z,Theta=theta)

def audit_circuit(path):
    body=read(path);profile=path.name.split('_')[0];kind=body['majorant']
    rebuilt=build(profile,kind,tuple(body['majorant_order']))
    require(body==rebuilt,'literal circuit regeneration '+path.name)
    nodes=body['nodes'];live=set();todo=[body['output']]
    while todo:
        n=todo.pop()
        if n in live:continue
        live.add(n);node=nodes[n]
        if node['kind'] in ('add','sub','mul'):
            require(0<=node['left']<n and 0<=node['right']<n,'acyclic register order')
            todo.extend((node['left'],node['right']))
    require(len(live)==len(nodes),'all nodes live')
    require(set(n['name'] for n in nodes if n['kind']=='variable')==set(body['variables']),'all nine inputs live')
    counts=Counter(n['kind'] for n in nodes if n['kind'] in ('add','sub','mul'))
    require(dict(counts)==body['operation_counts'] and sum(counts.values())==body['total_operations'],'operation count')
    nums=fixed(profile);ports=[int.from_bytes(gzip.decompress((ROOT/'data'/f'{s}.bin.gz').read_bytes()),'little') for s in ['beta','K','MC','MF_source']]
    if profile=='h1868':
        for name,rec in body['coefficient_recipes'].items():
            val=sum(t['coefficient']*math.prod(x**e for x,e in zip(ports,t['powers'])) for t in rec)
            require(nums[name]==val,'actual fixed coefficient recipe')
            require(abs(val)<2**2134927,'source coefficient height')
        require(nums['base_scale']==2**2134939 and nums['threshold_scale']==2**16012032,'exact scale leaves')
    rng=random.Random(20261023);samples=0
    for p in (1000000007,1000000009,2147483647):
        fs={n:x%p for n,x in nums.items()};ps=[x%p for x in ports]
        for trial in range(20):
            v={n:1 if trial==0 else rng.randrange(1,p) for n in body['variables']}
            got,regs=evaluate(body,fs,v,p)
            if profile=='h1868':
                direct=source_direct(v,ps,p)
                for n,x in direct.items():require(regs[n]==x,'independent source register '+n)
            else:
                parent=read(ROOT/'baseline/compact2082/parent.json')
                _,direct=evaluate(parent,fs,v,p)
                for n in ('R','N','A','K','P','Y','Omega','E0','V0','a0','J','C','B1'):
                    require(regs[n]==direct[n],'preserved compact source '+n)
            out,newregs=tail_direct(direct,v,p,kind)
            require(got==out,'independent full formula')
            for n,x in newregs.items():require(regs[n]==x,'independent tail register '+n)
            samples+=1
    a=body['named_degree_bounds']['A'];r=body['named_degree_bounds']['R'];W=body['W']
    om=5*a+2*W+3;v0=3*a+r+1;delta0=3*a+r+2
    if kind=='complete':
        v1=18*a+r+30;delta1=18*a+2*r+60
        candidates=[4*om+2*delta1,4*om+v0+v1+delta1,4*om+delta0+2*v1,4*om+2*v0+delta1]
        require(candidates[1]>max(candidates[0],candidates[2],candidates[3]),'unique final leading term')
    else:
        v1=18*a+r+24;delta1=34*a+2*r+48
        candidates=[4*om+2*delta1,4*om+v0+v1+delta1,4*om+delta0+2*v1,4*om+2*v0+delta1]
        require(candidates[0]>max(candidates[1:]),'unique simple leading term')
    require(max(candidates)==body['exact_degree'],'cancellation-aware exact degree')
    # E0^2 and E0*Omega*(V0+V1) are strictly lower in the inner reduced norm.
    e0=body['named_degree_bounds']['E0']
    require(2*om+delta1>max(2*e0,e0+om+max(v0,v1)),'inner leading degree')
    return dict(file=path.name,status='PASS',operations=sum(counts.values()),exact_degree=max(candidates),
                modular_formula_cases=samples,degree_candidates=candidates)

def main():
    report=dict(majorant=audit_majorant(),source=extraction(),circuits=[])
    for p in sorted((ROOT/'equations').glob('*.json')):report['circuits'].append(audit_circuit(p))
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
