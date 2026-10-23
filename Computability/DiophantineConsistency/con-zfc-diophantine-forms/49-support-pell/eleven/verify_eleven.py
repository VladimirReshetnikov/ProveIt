#!/usr/bin/env python3
"""Independent finite audits of the eleven-variable norm and exact leading form.

Requires NumPy only for full univariate polynomial rays. These checks do not
prove the inherited unbounded compiler semantics or consistency of ZFC.
"""
import gzip,hashlib,json,random
from pathlib import Path
import numpy as np
from build_eleven import build,evaluate,VARIABLES,PORTS

HERE=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise ValueError(message)

def load_coefficients():
    root=HERE.parent/'coefficients'
    binding=json.loads((root/'COEFFICIENT_BINDING.json').read_text()); ans={}
    for entry in binding['files']:
        packed=(root/entry['file']).read_bytes(); raw=gzip.decompress(packed)
        require(hashlib.sha256(raw).hexdigest()==entry['sha256'],'raw coefficient hash')
        require(hashlib.sha256(packed).hexdigest()==entry['gzip_sha256'],'gzip coefficient hash')
        value=int.from_bytes(raw,'little'); require(value.bit_length()==entry['bit_length'],'coefficient bits')
        ans[{'K':'K0','MF_source':'MF'}.get(entry['port'],entry['port'])]=value
    return ans

def direct_parameters(v,carrier):
    J,F,alpha,z,i,T,s,w,eta,zeta,t=[v[n] for n in VARIABLES]
    beta,K0,MC,MF=[v[n] for n in PORTS]
    q=beta*J+1; X=w*q; Y=(s+3*q)*q**3; E=X*Y; k=eta+zeta; c=k*Y+eta
    a=E+Y; H=4*a+3; Delta=a*a+H; ell=E*k*Y; A=1+ell*(ell+k); G=1+Delta*c*c
    b0=X+a*c; R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    Nt=(K0+w)*(q-F-alpha)+q-F-z*(q-1)
    I=i*c*c; D=1+Delta*I*I; Q=Delta*(D-1); d=Q-1; vv=c*T; b=c+R*D
    K=I*T+1; delta=(a+2)*c-ell if carrier=='full' else a*c-ell
    S=E*H; L=E*(1+H*K); W=E*b0+H*(E*(t+b+delta)+k-R-1)
    return dict(G=G,A=A,D=D,Q=Q,d=d,v=vv,b=b,S=S,L=L,W=W,Nt=Nt)

def independent_norm(params,prime=None):
    p=params
    def mul(x,y):
        out=[0]*8
        for j in range(8):
            for k in range(8):
                out[j^k]+=x[j]*y[k]*(p['G'] if j&k&1 else 1)*(p['A'] if j&k&2 else 1)*(p['D'] if j&k&4 else 1)
        return [v%prime for v in out] if prime else out
    out=[1]+[0]*7
    ee=p['Q']*(p['D']*p['v']**2+p['b']**2)-1; aux=2*p['Q']*p['v']*p['b']
    for sg in (-1,1):
      for st in (-1,1):
       for sf in (-1,1):
        lin=[p['W'],-sg*p['L'],-st*p['S'],0,0,0,0,0]
        factor=[p['d']*v for v in mul(lin,lin)]
        factor[0]-=p['S']**2*ee; factor[4]+=sf*p['S']**2*aux
        out=mul(out,factor)
    require(not any(out[1:]),'non-scalar formal product')
    return out[0]

def leading_norm(ray,prime,carrier):
    r=ray; q=r['beta']*r['J']%prime; k=r['eta']+r['zeta']; X=r['w']*q
    Y=(r['s']+3*q)*q**3; E=X*Y; c=k*Y; I=r['i']*c*c; H=4*E; ell=E*c
    d=E**4*I*I; B=q**3*(q-r['F'])*E**2*I**2; V=I*r['T']*ell
    common=pow(E,16,prime)*pow(H,16,prime)*pow(d,8,prime)*pow(B,8,prime)*pow(V,4,prime)*ell**2*k*Y**2
    if carrier=='full': norm=-2**14*common*(2*r['t']+k-r['i']*r['T']*c*pow(E,-1,prime))
    else: norm=2**16*common*c
    return norm%prime

def degree_ray(packet,prime,seed,ports):
    rng=random.Random(seed)
    env={v:np.array([0,rng.randrange(1,prime)],dtype=np.int64) for v in VARIABLES}
    env.update({v:np.array([ports[v]%prime],dtype=np.int64) for v in PORTS})
    ray={v:int(z[-1]) for v,z in env.items()}
    def trim(x):
        x=x%prime
        while len(x)>1 and not x[-1]: x=x[:-1]
        return x
    for name,op,x,y in packet['source']:
        x=np.array([x],dtype=np.int64) if isinstance(x,int) else env[x]
        y=np.array([y],dtype=np.int64) if isinstance(y,int) else env[y]
        if op=='*': z=np.convolve(x,y)
        else:
            z=np.zeros(max(len(x),len(y)),dtype=np.int64); z[:len(x)]+=x; z[:len(y)]+=y if op=='+' else -y
        env[name]=trim(z)
    value=env[packet['output']]; degree=len(value)-1
    require(degree==packet['exact_degree'],'ray degree '+str((degree,packet['exact_degree'])))
    q0=ray['beta']*ray['J']; Nt=ray['w']*(q0-ray['F']-ray['alpha'])-ray['z']*q0
    predicted=leading_norm(ray,prime,packet['carrier'])*Nt%prime
    require(predicted==int(value[-1]) and predicted!=0,'leading form coefficient')
    return dict(prime=prime,seed=seed,degree=degree,leading_coefficient=predicted,analytic_leading_form_matches=True)

def main():
    actual=load_coefficients(); rng=random.Random(990)
    result={'coherent_source31_payload_hashes':'PASS','scope':'Finite identities, coefficient binding and degree diagnostics; ordinary unbounded proof is separate.','carriers':{}}
    for car in ('full','short'):
        packet=build('product',car)
        for _ in range(16):
            vals={v:rng.randrange(-2,4) for v in VARIABLES+PORTS}
            env=evaluate(packet,vals); direct=direct_parameters(vals,car)
            require(env['Nt']==direct['Nt'],'transport definition')
            require(env['N']==independent_norm(direct),'exact formal norm')
            require(env['N']%4 in (0,1),'mod-four guard')
        for _ in range(40):
            prime=1000000007; vals={v:rng.randrange(prime) for v in VARIABLES+PORTS}
            env=evaluate(packet,vals,prime); direct=direct_parameters(vals,car)
            require(env['N']==independent_norm(direct,prime),'modular formal norm')
        for _ in range(12):
            vals={v:rng.randrange(-2,4) for v in VARIABLES+PORTS}; old=dict(vals); old['z']+=1
            lhs=evaluate(build('system',car),old); rhs=evaluate(build('shifted_system',car),vals)
            require(lhs['Nt']-1==rhs['transleft']-rhs['transright'],'transport shift')
            require(lhs['term1']==rhs['term1'] and lhs['term2']==rhs['term2'],'norm unchanged by transport shift')
        rays=[degree_ray(packet,10007,991,dict(zip(PORTS,[31,127,10,45]))),degree_ray(packet,10009,992,actual),degree_ray(packet,10037,993,actual)]
        result['carriers'][car]={'ledger':packet['ledger'],'exact_integer_formal_products':16,'modular_formal_products':40,'transport_shift_checks':12,'full_polynomial_rays':rays}
    out=HERE/'generated'; out.mkdir(exist_ok=True)
    (out/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
