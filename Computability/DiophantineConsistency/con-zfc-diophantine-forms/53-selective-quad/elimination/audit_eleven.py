#!/usr/bin/env python3
"""Independent rank-eight diagnostic of denominator-Y carrier, no upstream imports."""
import gzip,hashlib,json,random
from pathlib import Path
HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'batching'
P=1000000007

def add(x,y):return [(a+b)%P for a,b in zip(x,y)]
def neg(x):return [(-a)%P for a in x]
def scalar(x):return [x%P]+[0]*7
def scale(x,n):return [a*n%P for a in x]
def mul(x,y,r):
    z=[0]*8
    for a,xa in enumerate(x):
        for b,yb in enumerate(y):
            c=xa*yb
            overlap=a&b
            for i in range(3):
                if overlap>>i&1:c=c*r[i]
            z[a^b]=(z[a^b]+c)%P
    return z

def literals(v):
    J,F,alpha,z,i,T,s,w,eta,zeta,t=(v[n] for n in ['J','F','alpha','z','i','T','s','w','eta','zeta','t'])
    beta,K0,MC,MF=(v[n] for n in ['beta','K0','MC','MF'])
    q=beta*J+1;Y=(s+3*q)*q**3;X=w*q;E=X*Y;k=eta+zeta;c=k*Y+eta;a=E+Y
    H=4*a+3;Delta=a*a+H;ell=E*k*Y;A=1+ell*(ell+k);G=1+Delta*c*c;b0=X+a*c
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    I=i*c*c;D=1+Delta*I*I;Q=Delta*(D-1);d=Q-1;vv=c*T;b=c+R*D
    e=Q*(D*vv*vv+b*b)-1;Baux=2*Q*vv*b;K=I*T+1;L0=1+H*K
    return {n:x%P for n,x in locals().items() if isinstance(x,int)}

def formal(v,car,old=False):
    a=literals(v)
    H,Y,b0,b,ell,d,e,Baux,A,G,D,L0,k,R,t=(a[n] for n in ['H','Y','b0','b','ell','d','e','Baux','A','G','D','L0','k','R','t'])
    delta=((a['a']+(2 if car=='full' else 0))*a['c']-ell)%P
    if old:
        t=(t+(k-R-1)*pow(Y,-1,P))%P
        S=H;L=L0;W=(b0+H*(t+b+delta))%P
    else:
        S=H*Y%P;L=Y*L0%P;W=(Y*(b0+H*(t+b+delta))+H*(k-R-1))%P
    rr=[G,A,D];ans=scalar(1)
    for sg in [-1,1]:
      for st in [-1,1]:
       for sf in [-1,1]:
        z=scalar(W);z[1]=-L*sg%P;z[2]=-S*st%P
        factor=scale(mul(z,z,rr),d)
        factor[0]=(factor[0]-S*S*e)%P
        factor[4]=(factor[4]+S*S*Baux*sf)%P
        ans=mul(ans,factor,rr)
    if any(ans[1:]):raise AssertionError('formal radicals did not cancel')
    return ans[0]

def circuit(c,v):
    a=dict(v)
    for n,op,x,y in c['source']:
        x=a[x] if isinstance(x,str) else x;y=a[y] if isinstance(y,str) else y
        a[n]=((x+y) if op=='+' else (x-y) if op=='-' else (x*y))%P
    return a

def main():
    r=random.Random(7958);count=0;ident=0;guard=0
    binding=json.loads((SOURCE/'COEFFICIENT_BINDING.json').read_text());ports={}
    vals={}
    for row in binding['payloads']:
        raw=gzip.decompress((SOURCE/row['path']).read_bytes())
        if hashlib.sha256(raw).hexdigest()!=row['sha256']:raise AssertionError('payload')
        vals[row['name']]=int.from_bytes(raw,'little')%P
    ports={p:vals[n] for p,n in binding['port_aliases'].items()}
    for car in ['full','short']:
      c=json.loads((SOURCE/(car+'_product.json')).read_text())
      for j in range(180):
        v={n:r.randint(-5,8) for n in c['witnesses']}
        v.update(ports if j%2 else {n:r.randint(-3,9) for n in c['fixed_numerals']})
        got=circuit(c,v);want=formal(v,car)
        if got['N']!=want:raise AssertionError((car,j,'norm'))
        if got['polynomial']!=(got['Nt']*(1+want)-1)%P:raise AssertionError('product')
        count+=1
        a=literals(v)
        if a['Y']:
            if want!=pow(a['Y'],16,P)*formal(v,car,True)%P:raise AssertionError('scale identity')
            ident+=1
    result={'status':'PASS','formal_factor_comparisons':count,'rational_carrier_identity_checks':ident,'prime':P,'seed':7958,'actual_payloads_verified':True,'scope':'Finite algebra diagnostics only; unbounded proof manually reviewed separately.'}
    (HERE/'AUDIT_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
