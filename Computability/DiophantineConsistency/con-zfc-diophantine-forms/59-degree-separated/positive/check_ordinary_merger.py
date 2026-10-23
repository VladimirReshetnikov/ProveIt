#!/usr/bin/env python3
"""Independent inert-circuit checks and full finite-field polynomial rays."""
import json,random,gzip,hashlib
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent
VARS=['J','F','alpha','z','f0','T','s','w','eta','zeta','gamma','t']
PORTS=['beta','K0','MC','MF']
def require(x,msg):
    if not x:raise AssertionError(msg)
def evaluate(p,vals,prime=None):
    e=dict(vals)
    for n,op,x,y in p['source']:
        x=x if isinstance(x,int) else e[x];y=y if isinstance(y,int) else e[y]
        z=x+y if op=='+' else x-y if op=='-' else x*y
        e[n]=z if prime is None else z%prime
    return e
def algebra_mul(x,y,rad,prime=None):
    out=[0]*len(x)
    for j,a in enumerate(x):
      for k,b in enumerate(y):
        fac=1
        for bit,r in enumerate(rad):
            if (j&k)&(1<<bit):fac*=r
        out[j^k]+=a*b*fac
    return [a%prime for a in out] if prime else out
def independent_inner(e,prime=None):
    out=[1,0,0,0];rad=[e['Q'],e['A']]
    for sr in [-1,1]:
      for st in [-1,1]:
        v=[e['c2']*e['t'],-sr,-st*e['c2']*e['f'],0]
        row=[e['d']*z for z in algebra_mul(v,v,rad,prime)];row[0]-=e['c4']*(2*e['f']*e['ell'])**2*e['Eaux']
        out=algebra_mul(out,row,rad,prime)
    require(not any(out[1:]),'non-scalar two-radical product');return out[0]
def independent_full_linear(e,prime=None):
    rad=[e['Q'],e['A'],e['d']*e['Eaux']];out=[1]+[0]*7
    for sr in [-1,1]:
      for st in [-1,1]:
       for sy in [-1,1]:
        row=[e['c2']*e['d']*e['t'],-sr*e['d'],-st*e['c2']*e['d']*e['f'],0,-sy*e['c2']*(2*e['f']*e['ell']),0,0,0]
        out=algebra_mul(out,row,rad,prime)
    require(not any(out[1:]),'non-scalar three-radical product');return out[0]
def bound_ports():
    b=json.loads((HERE/'COEFFICIENT_BINDING.json').read_text());values={}
    for p in b['payloads']:
        rawgz=(HERE/p['path']).read_bytes();raw=gzip.decompress(rawgz)
        require(hashlib.sha256(rawgz).hexdigest()==p['gzip_sha256'],'packed hash')
        require(hashlib.sha256(raw).hexdigest()==p['sha256'],'raw hash')
        value=int.from_bytes(raw,'little');require(value.bit_length()==p['bit_length'] and len(raw)==p['bytes'],'coefficient dimensions');values[p['name']]=value
    return {port:values[name] for port,name in b['port_aliases'].items()}
def expected_leaders(r,p):
    q=r['beta']*r['J'];Y=r['s']*q**3;E=r['w']*q*Y;c=(r['eta']+r['zeta'])*Y
    inner=pow(2,8,p)*pow(E,16,p)*pow(c,32,p)*pow(r['T'],8,p)*pow(r['f0'],24,p)%p
    main=128*pow(q,8,p)*E**2*c*r['gamma']%p
    nt=(r['w']*(q-r['F']-r['alpha'])-r['z']*q)%p
    return nt,main,inner
def polynomial_ray(doc,prime,seed,ports):
    rng=random.Random(seed);e={v:np.array([0,rng.randrange(1,prime)],dtype=np.int64) for v in VARS}
    e.update({v:np.array([ports[v]%prime],dtype=np.int64) for v in PORTS});r={v:int(x[-1]) for v,x in e.items()}
    def trim(z):
        z=z%prime
        while len(z)>1 and z[-1]==0:z=z[:-1]
        return z
    def sub(x,y):
        z=np.zeros(max(len(x),len(y)),dtype=np.int64);z[:len(x)]+=x;z[:len(y)]-=y;return trim(z)
    for n,op,x,y in doc['source']:
        x=np.array([x],dtype=np.int64) if isinstance(x,int) else e[x];y=np.array([y],dtype=np.int64) if isinstance(y,int) else e[y]
        if op=='*':z=np.convolve(x,y)
        else:
            z=np.zeros(max(len(x),len(y)),dtype=np.int64);z[:len(x)]+=x;z[:len(y)]+=y if op=='+' else -y
        e[n]=trim(z)
    nt,main,inner=expected_leaders(r,prime)
    if 'output' in doc:
        out=e[doc['output']];leader=nt*main*inner%prime if doc['presentation']=='product' else inner*inner%prime
        require(len(out)-1==doc['exact_degree'],('degree',doc['name'],len(out)-1));require(int(out[-1])==leader,('leader',doc['name']))
        degs=[len(out)-1]
    else:
        degs=[]
        for (left,right),deg,leader in zip(doc['comparisons'],[2,26,288],[nt,main,inner]):
            x=e[left] if isinstance(left,str) else np.array([left]);y=e[right] if isinstance(right,str) else np.array([right]);out=sub(x,y)
            require(len(out)-1==deg,('residual degree',doc['name'],len(out)-1,deg));require(int(out[-1])==leader,('residual leader',doc['name'],deg));degs.append(deg)
    return {'prime':prime,'seed':seed,'exact_degrees':degs,'analytic_leaders_match':True}
def diagnostics():
    count=0
    for q in [16,17,31,101]:
      for w in [1,10,10**5,10**12]:
       for ss in [1,10,10**6]:
        for eta,zeta in [(1,1),(2,3),(10**6,1)]:
         X=w*q;Y=ss*q**3;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y;ell=E*k*Y
         require(a+2<2*E and ell-k>a+2,'uniform radical separation bounds')
         require(4*q**4>q**4 and Y>=q**3,'absorber size');count+=1
    return count
def main():
    actual=bound_ports();docs={p:json.loads((HERE/('ordinary_merger_'+p+'.json')).read_text()) for p in ['product','system','shifted_system','sos']}
    result={'scope':'Finite algebra, leading-degree, and bound diagnostics; not an unbounded compiler proof.','coefficient_hashes':True,'formal_integer_cases':36,'formal_modular_cases':100,'bound_cases':diagnostics(),'rays':{}}
    doc=docs['product'];rng=random.Random(316)
    for j in range(36):
        vals={v:rng.randrange(-2,4) for v in VARS+PORTS};e=evaluate(doc,vals)
        require(e['Ninner']==independent_inner(e),'integer inner identity');require(independent_full_linear(e)==e['d']**4*e['Ninner'],'denominator deflation identity')
        require(e['Ninner']%16 in [0,1,4,9],'inner square mod16');require(e['Nmain']%16 in [0,1,4,9],'main square mod16')
    for j in range(100):
        prime=1000000007;vals={v:rng.randrange(prime) for v in VARS+PORTS};e=evaluate(doc,vals,prime)
        require(e['Ninner']==independent_inner(e,prime),'modular inner identity');require(independent_full_linear(e,prime)==pow(e['d'],4,prime)*e['Ninner']%prime,'modular deflation')
    for name,doc in docs.items():
        result['rays'][name]={}
        for tag,ports in [('illustrative',dict(zip(PORTS,[31,127,10,45]))),('actual',actual)]:
            result['rays'][name][tag]=[polynomial_ray(doc,p,se,ports) for p,se in [(10007,316),(10009,317),(10037,318)]]
    for j in range(24):
        vals={v:rng.randrange(-2,4) for v in VARS+PORTS};old=dict(vals);old['z']+=1;a=evaluate(docs['system'],old);b=evaluate(docs['shifted_system'],vals)
        require(a['Nt']-1==b['transleft']-b['transright'],'shift transport')
        require(a['mainleft']-a['mainright']==b['mainleft']-b['mainright'],'shift main')
        require(a['innerleft']-a['innerright']==b['innerleft']-b['innerright'],'shift inner')
    result['transport_shift_cases']=24
    (HERE/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
