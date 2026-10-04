#!/usr/bin/env python3
"""Own read-only checker for the emitted source, not an upstream replay."""
import hashlib
import json
from pathlib import Path


ROOT=Path(__file__).resolve().parent


def require(test, message):
    if not test: raise RuntimeError(message)


def evaluate(source, values, modulus):
    env={'input:InputPlus':values['InputPlus']%modulus}
    for name in source['witnesses']:
        require(values[name]>0,'nonpositive witness '+name)
        env['witness:'+name]=values[name]%modulus
    def get(ref):
        return int(ref[9:])%modulus if ref.startswith('constant:') else env[ref]
    for i,(op,a,b) in enumerate(source['gates']):
        a,b=get(a),get(b)
        value=a+b if op=='+' else a-b if op=='-' else a*b
        env['gate:'+str(i)]=value%modulus
    return get


def direct_power(values, name, base, exponent):
    def v(s):return values[name+'.'+s]
    a,beta=v('A0')+1,v('B0')+1
    w,mod,g,x,y,u,vv,s,t=[v(k) for k in ('w','mod','g','x','y','u','v','s','t')]
    k=exponent+1; m=base*v('out')
    nat=lambda s:v(s+'.Plus')-1
    return [
        x*x-1-(a*a-1)*y*y,
        u*u-1-(a*a-1)*vv*vv,
        s*s-1-(beta*beta-1)*t*t,
        beta-1-4*y*v('qb'),
        beta+u*nat('alpha1')-a-u*nat('alpha2'),
        vv-y*y*v('qv'),
        s+u*nat('sigma1')-x-u*nat('sigma2'),
        t+4*y*nat('tau1')-k-4*y*nat('tau2'),
        y-k-nat('dyk'),w-base-nat('dwb'),w-k-nat('dwk'),
        mod-m-v('S'),a*a-1-((w+1)*(w+1)-1)*(w*g)*(w*g),
        2*a*base-mod-base*base-1,
        x+mod*nat('rho1')-y*(a-base)-m-mod*nat('rho2'),
    ]


def check_emission(source):
    equation_map={name:(left,right) for left,right,name in source['equalities']}
    require(len(equation_map)==len(source['equalities']),'duplicate equations')
    counts={'power_residuals':0,'subset_residuals':0,'single_polynomial_checks':0}
    for trial,modulus in enumerate((101,1009,65537,1000003),1):
        values={name:1+((i+17)*(trial+11)*37)%89 for i,name in enumerate(source['witnesses'])}
        values['InputPlus']=19+trial
        get=evaluate(source,values,modulus)
        for macro in source['macros']:
            name=macro['name']
            if macro['kind']=='power':
                wanted=direct_power(values,name,get(macro['base']),get(macro['exponent']))
                for i,residual in enumerate(wanted,1):
                    left,right=equation_map[name+'.eq'+str(i)]
                    require((get(left)-get(right)-residual)%modulus==0,'power substitution '+name)
                    counts['power_residuals']+=1
            elif macro['kind']=='subset':
                L,Y,Z=[values[name+'.'+s+'.out'] for s in ('L','Y','Z')]
                q,o,r=[values[name+'.'+s+'.Plus']-1 for s in ('q','o','r')]
                wanted=[Z-(q*L+2*o+1)*Y-r,2*o+1+values[name+'.sc']-L,r+values[name+'.sr']-Y]
                for suffix,residual in zip(('extract','digit_bound','remainder_bound'),wanted):
                    left,right=equation_map[name+'.'+suffix]
                    require((get(left)-get(right)-residual)%modulus==0,'subset substitution '+name)
                    counts['subset_residuals']+=1
        expected=sum((get(a)-get(b))**2 for a,b,_ in source['equalities'])%modulus
        require(get(source['output'])==expected,'single polynomial mismatch')
        counts['single_polynomial_checks']+=1
    return counts


def pell(a,n):
    def product(u,v):return (u[0]*v[0]+(a*a-1)*u[1]*v[1],u[0]*v[1]+u[1]*v[0])
    result,power=(1,0),(a,1)
    while n:
        if n&1: result=product(result,power)
        power=product(power,power);n//=2
    return result


def genuine_power(base,exponent):
    k=exponent+1;out=base**exponent;w=max(base,k)
    a,ygrowth=pell(w+1,w);require(ygrowth%w==0,'growth quotient')
    g=ygrowth//w;x,y=pell(a,k);u,v=pell(a,2*k*y)
    beta=a+u*(((1-a)*pow(u,-1,4*y))%(4*y))
    s,t=pell(beta,k);mod=2*a*base-base*base-1;m=base*out
    raw={'out':out,'w':w,'A0':a-1,'mod':mod,'g':g,'x':x,'y':y,'u':u,'v':v,'s':s,'t':t,
         'B0':beta-1,'dwb.Plus':w-base+1,'dwk.Plus':w-k+1,'dyk.Plus':y-k+1,
         'S':mod-m,'qb':(beta-1)//(4*y),'qv':v//(y*y)}
    for left,right,divisor,prefix in ((beta,a,u,'alpha'),(s,x,u,'sigma'),(t,k,4*y,'tau'),(x,y*(a-base)+m,mod,'rho')):
        require((right-left)%divisor==0,'congruence construction')
        quotient=(right-left)//divisor
        raw[prefix+'1.Plus']=max(quotient,0)+1
        raw[prefix+'2.Plus']=max(-quotient,0)+1
    values={'test.'+name:value for name,value in raw.items()}
    require(len(values)==26,'power witness/output count')
    require(all(v>0 for v in values.values()),'positive Pell witnesses')
    require(all(v==0 for v in direct_power(values,'test',base,exponent)),'genuine Pell residual')
    return {'base':base,'exponent':exponent,'output':out,'max_witness_bits':max(v.bit_length() for v in values.values())}


def check_domains():
    # These exhaust minimal/small positive dimensions; proof supplies all sizes.
    cases=0
    for p in (1,2):
      for q in (1,2):
       for r in (1,2):
        for d in (1,2):
         for e in (1,2):
          for f in (1,2):
            tx=max(2,q*r+1,e*f+1);ty=max(2,r+1,f+1);tz=2
            ax,ay,az=p*d*tx,q*e*ty,r*f*tz;A,B,C=2*ax,2*ay,2*az
            specs=((p,q*r,2*d*tx),(A*q,r,2*e*ty),(d,e*f,2*p*tx),(A*e,f,2*q*ty))
            for exponent,n,stride in specs:
                require(exponent>=1 and n>=1 and stride>=n+1,'spread macro domain')
                require(stride-1>=1,'copy exponent domain')
            require(min(A,B,C)>=4,'interior mask domain')
            require(1<=ax<=ax+d-1<=A-2,'x containment')
            require(1<=ay<=ay+e-1<=B-2,'y containment')
            require(1<=az<=az+f-1<=C-2,'z containment')
            cases+=1
    return cases


def check_pairing():
    def pair(a,b):return (a+b)*(a+b+1)//2+b
    def unpair(n):
        import math
        s=(math.isqrt(8*n+1)-1)//2;b=n-s*(s+1)//2
        return s-b,b
    cases=0
    for j in range(100):
        fields=[(j*(i+3)+i)%17 for i in range(8)]
        code=fields[-1]
        for a in fields[-2::-1]:code=pair(a,code)
        rest=code;decoded=[]
        for _ in range(7):a,rest=unpair(rest);decoded.append(a)
        decoded.append(rest);require(decoded==fields,'pairing inverse');cases+=1
    return cases


def main():
    raw=(ROOT/'evidence/polynomial-dag.json').read_bytes();source=json.loads(raw)
    receipt={'emission':check_emission(source),'domain_fixtures':check_domains(),'pairing_fixtures':check_pairing(),
             'genuine_power_witnesses':[genuine_power(b,e) for b,e in ((2,0),(2,1),(3,0),(3,1),(32,0))],
             'polynomial_dag_sha256':hashlib.sha256(raw).hexdigest(),
             'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
             'scope':'No full giant certificate witnesses instantiated; all-length power soundness uses the pinned theorem.'}
    path=ROOT/'evidence/source-check-receipt.json';path.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2,sort_keys=True))


if __name__=='__main__':main()
