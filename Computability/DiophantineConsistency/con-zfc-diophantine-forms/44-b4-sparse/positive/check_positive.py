#!/usr/bin/env python3
"""Independent formal-algebra identities and complete modular polynomial rays."""
import json,random
from pathlib import Path
import numpy as np
from build_positive import build,VARIABLES,PORTS,verify_binding
HERE=Path(__file__).resolve().parent
def require(condition,message):
    if not condition:raise AssertionError(message)
def evaluate(p,vals,prime=None):
    env=dict(vals)
    for n,op,x,y in p['source']:
        x=x if isinstance(x,int) else env[x];y=y if isinstance(y,int) else env[y]
        v=x+y if op=='+' else x-y if op=='-' else x*y
        env[n]=v if prime is None else v%prime
    return env
def independent_norm(e,prime=None):
    def mul(x,y):
        z=[0]*8
        for j in range(8):
            for k in range(8):
                z[j^k]+=x[j]*y[k]*(e['G'] if j&k&1 else 1)*(e['A'] if j&k&2 else 1)*(e['D'] if j&k&4 else 1)
        return [v%prime for v in z] if prime else z
    ans=[1]+[0]*7;ee=e['Q']*(e['D']*e['v']**2+e['b']**2)-1;B=2*e['Q']*e['v']*e['b']
    for sg in [-1,1]:
      for st in [-1,1]:
       for sf in [-1,1]:
        z=[e['W'],-sg*e['L'],-st*e['H'],0,0,0,0,0]
        row=[e['d']*v for v in mul(z,z)];row[0]-=e['H']**2*ee;row[4]+=sf*e['H']**2*B
        ans=mul(ans,row)
    require(not any(ans[1:]),'formal radical product not scalar');return ans[0]
def degree_ray(p,prime,seed,ports=None):
    rng=random.Random(seed);env={v:np.array([0,rng.randrange(1,prime)],dtype=np.int64) for v in VARIABLES}
    ports=ports or dict(zip(PORTS,[31,127,10,45]))
    env.update({v:np.array([ports[v]%prime],dtype=np.int64) for v in PORTS})
    ray={v:int(a[-1]) for v,a in env.items()}
    def trim(a):
        a=a%prime
        while len(a)>1 and a[-1]==0:a=a[:-1]
        return a
    for n,op,x,y in p['source']:
        x=np.array([x],dtype=np.int64) if isinstance(x,int) else env[x];y=np.array([y],dtype=np.int64) if isinstance(y,int) else env[y]
        if op=='*':z=np.convolve(x,y)
        else:
            z=np.zeros(max(len(x),len(y)),dtype=np.int64);z[:len(x)]+=x;z[:len(y)]+=y if op=='+' else -y
        env[n]=trim(z)
    out=env[p['output']];degree=len(out)-1
    require(degree==p['exact_degree'],(p['name'],degree,p['exact_degree']))
    predicted=leading_form(p,ray,prime)
    require(int(out[-1])==predicted,('leading form',p['name'],int(out[-1]),predicted))
    return {'prime':prime,'seed':seed,'degree':degree,'leading_coefficient':int(out[-1]),'analytic_leading_form_matches':True,'ray':ray}
def leading_form(p,r,prime):
    q=r['beta']*r['J'];k=r['eta']+r['zeta'];X=r['w']*q;Y=r['s']*q**3;E=X*Y;c=k*Y
    I=r['i']*c*c;H=4*E;ell=E*c;d=E**4*I**2;B=q**3*(q-r['F'])*E**2*I**2;V=I*r['T']*ell
    common=pow(H,16,prime)*pow(d,8,prime)*pow(B,8,prime)*pow(V,4,prime)*ell**2*k*Y**2
    if p['carrier']=='short':norm=2**16*common*c
    else:norm=-2**14*common*(2*r['t']+k-r['i']*r['T']*c*pow(E,-1,prime))
    Nk=-r['h']*E;Nt=r['w']*(q-r['F']-r['alpha'])-r['z']*q
    return norm*Nk*Nt%prime
def main():
    actual=verify_binding()
    result={'selected_tuple_hashes_verified':True,'exact_integer_formal_products':{},'modular_formal_products':{},'full_polynomial_ray_checks':{},'actual_fixed_tuple_ray_checks':{},'scope':'Finite algebra diagnostics; no compiler or consistency proof.'}
    for car in ['short','full']:
        p=build(car,'product');rng=random.Random(901)
        for j in range(24):
            vals={v:rng.randrange(-2,4) for v in VARIABLES+PORTS};e=evaluate(p,vals)
            require(e['N']==independent_norm(e),'integer norm identity');require(e['N']%4 in [0,1],'unit congruence')
        result['exact_integer_formal_products'][car]=24
        for j in range(60):
            prime=1000000007;vals={v:rng.randrange(prime) for v in VARIABLES+PORTS};e=evaluate(p,vals,prime)
            require(e['N']==independent_norm(e,prime),'modular norm identity')
        result['modular_formal_products'][car]=60
        result['full_polynomial_ray_checks'][car]=[degree_ray(p,prime,seed) for prime,seed in [(10007,901),(10009,902),(10037,903)]]
        result['actual_fixed_tuple_ray_checks'][car]=[degree_ray(p,prime,seed,actual) for prime,seed in [(10007,904),(10009,905),(10037,906)]]
        old=build(car,'system');new=build(car,'shifted_system')
        for j in range(24):
            vals={v:rng.randrange(-2,4) for v in VARIABLES+PORTS};vold=dict(vals);vold['z']+=1;eold=evaluate(old,vold);enew=evaluate(new,vals)
            require(eold['Nt']-1==enew['transleft']-enew['transright'],'transport shift')
            require(eold['term1']==enew['term1'] and eold['term2']==enew['term2'],'carrier unchanged')
    result['transport_shift_checks_per_carrier']=24
    (HERE/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
