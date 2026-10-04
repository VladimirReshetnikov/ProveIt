#!/usr/bin/env python3
"""Data-only width and factor-free period criteria; no source-code imports."""
import argparse
import hashlib
import json
from math import comb, gcd
from pathlib import Path

PINS = {
  "complete83_independent_gamma_scout.py": "b67ee981d5475a745094924d6ec3cbe72dfb38e3d28d9bd2c144ff0c2a59dc18",
  "complete83_independent_gamma_scout.json": "ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20",
  "complete83_independent_gamma_scout.md": "bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41",
  "complete84_scaled_strong_output.json": "8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf",
  "complete75_half_binomial_compiler.md": "68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117",
  "complete75_independent_gamma87_period.md": "dfe1c4a9c438bfe3907b187a3d407280616a5a7eaaf3aa68048de9938b8ac784",
  "complete75_gamma87_compiler_order_filters.md": "43d613204d6dc7192763e87e120f84ea0e3f18849a4fd23be26f56ca45b9fcc3",
  "complete75_bounded_projection_elimination99.md": "381dfecd4b608069a67a43f163d1c1c2b9ff4fcd4ed4d9409e03f45d1fbc24af"
}

def need(ok, message):
    if not ok: raise ValueError(message)

def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def sha(data): return hashlib.sha256(data).hexdigest()

def v2(n):
    need(n>0,'valuation domain')
    return (n & -n).bit_length()-1

def order2(H):
    z,O=2%H,1
    while z!=1:
        z=2*z%H;O+=1
        need(O<H,'order loop')
    return O

def pell(A,n):
    D=A*A-1
    x,y,bx,by=1,0,A,1
    while n:
        if n&1: x,y=x*bx+D*y*by,x*by+y*bx
        bx,by=bx*bx+D*by*by,2*bx*by
        n//=2
    return x,y

def verify(root):
    for name,pin in PINS.items():
        need(sha((root/name).read_bytes())==pin,'pin '+name)
    scout=json.loads((root/'complete83_independent_gamma_scout.json').read_text())
    need(scout['packet']['ledger']['total']==83 and scout['packet']['ledger']['M']==47,'actual parent source')
    need(len(scout['packet']['witnesses'])==18 and scout['packet']['exact_degree']==187,'actual parent interface')
    rows=scout['packet']['source']
    need(['gam','*','sigma','a4m5'] in rows,'independent gamma')
    need(['marked_rhs','-','C_after_alpha','scaled_t'] in rows,'retained input width')
    # Formal polynomial coefficients, increasing degree in a.
    Delta=[3,4,1]
    product=[7,16,4] # (2a+1)(2a+7)
    need([4*Delta[j]-product[j] for j in range(3)]==[5,0,0],'resultant identity')
    component_records=[]
    generic_tests=successful_tests=0
    for j in range(1,257):
        a=6*j;D=(a+1)*(a+3);H=4*a+3;O=order2(H);g=gcd(2*D,O)
        G1,G3=gcd(2*D,H-1),gcd(2*D,H-3)
        need(G1==(10 if a%5==2 else 2) and G3==6,'exact gcd identities')
        need(v2(g)==1,'exact two part')
        certs={}
        for d in (5,25,125):
            m=g//gcd(g,2*d)
            need(m%2==1,'odd alias modulus')
            for k in range(1,17):
                for offset,mult in ((1,1),(3,3)):
                    E=k*(H-offset)
                    passed=pow(2,E,H)==1
                    need(passed==(E%O==0),'independent modular exponent test')
                    if passed:
                        need(mult*(k>>v2(k))%m==0,'factor-free period implication')
                        successful_tests+=1
                    generic_tests+=1
            if d==5:
                for offset,mult in ((1,1),(3,3)):
                    hits=[e for e in range(6) if pow(2,(1<<e)*(H-offset),H)==1]
                    if hits:
                        need(mult%m==0,'fixed downward input shift')
                    certs[str(offset)]=hits
        component_records.append({'a':a,'H':H,'order':O,'g':g,
                                  'm_at_d5':g//gcd(g,10),'power_two_certificate_exponents':certs})
    # Exact finite interval theorem, independently enumerated.
    width_cases=0
    for d in (1,5,25):
        for alpha in range(1,41):
            for x0 in range(1,13):
                for m in range(1,13):
                    A=(alpha-1)//(2*d)
                    observed=[x for x in range(1,x0+A+1) if (x-x0)%m==0]
                    expected=1+(x0-1)//m+A//m
                    need(len(observed)==expected,'fiber cardinality')
                    need((len(observed)>1)==(m<=max(x0-1,A)),'exact width threshold')
                    need(all(alpha+2*d*(x0-x)>0 for x in observed),'positive alpha')
                    width_cases+=1
    explicit=[]
    for a,offset,shift in ((12,3,3),(48,3,3),(1092,1,1)):
        d,b,x0,alpha=5,5,4,1
        D=(a+1)*(a+3);H=4*a+3;O=order2(H);g=gcd(2*D,O)
        m=g//gcd(g,2*d);x=x0-shift
        need(pow(2,H-offset,H)==1 and shift%m==0 and x>0 and x%2==1,'explicit downward component')
        moved_alpha=alpha+2*d*shift
        u0,u=2*d*x0+b,2*d*x+b
        r=next(t for t in range(O//g) if (u+2*D*t-u0)%O==0)
        n=u+2*D*r
        while n<=max(u,u0):n+=2*D*(O//g)
        rec={'a':a,'Delta':D,'H':H,'order':O,'g':g,'m':m,'offset':offset,
             'x0':x0,'x':x,'alpha':alpha,'moved_alpha':moved_alpha,'u0':u0,'u':u,'Pell_index':n,
             'scope':'Pell/input component only; not a full compiler history or zero.'}
        if a in (12,48):
            chi,psi=pell(a+2,n);W=1<<u0
            delta,rem=divmod(psi-u,D);rho,rem2=divmod(chi-a*psi-W,H)
            need(not rem and not rem2 and min(delta,rho)>0,'strict positive component')
            need(chi*chi-D*psi*psi==1 and chi==W+a*(u+delta*D)+rho*H,'complete input norm')
            rec['materialized_input_component']={'chi_bits':chi.bit_length(),'psi_bits':psi.bit_length(),
                'delta_bits':delta.bit_length(),'rho_bits':rho.bit_length(),
                'values_sha256':sha(('|'.join(hex(z) for z in (chi,psi,delta,rho))).encode())}
        else:
            rec['materialized_input_component']=None
        explicit.append(rec)
    half=[]
    for R in (7,11,15,19,23,27,31,63):
        X=1<<R;r=(R-1)//2
        Y=sum(comb(2*r,r+j)*X**j for j in range(r+1))//2
        a=Y*(X+1);H=4*a+3
        need(a%6==0 and v2(a)==R.bit_count()-2,'native half-binomial valuation')
        half.append({'R':R,'popcount':R.bit_count(),'a_bits':a.bit_length(),'v2_a':v2(a),
            'H_bits':H.bit_length(),'a_H_sha256':sha((hex(a)+'|'+hex(H)).encode()),
            'power_two_certificate_exponents':{str(offset):[e for e in range(4) if pow(2,(1<<e)*(H-offset),H)==1] for offset in (1,3)},
            'compiler_history':False})
    return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':dict(PINS),
        'scope':'Conditional factor-free alias criteria, not a compiler-history existence theorem or a language refutation.',
        'parent_source':{'total':83,'M':47,'A':36,'witnesses':18,'degree':187},
        'gcd_components':component_records,'generic_period_tests':generic_tests,
        'successful_period_tests':successful_tests,'exact_width_cases':width_cases,
        'explicit_downward_components':explicit,'half_binomial_arithmetic_samples':half,
        'full_compiler_histories_materialized':0,'new_complete_source_emitted':False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path)
    a=p.parse_args();need(a.output is not None or a.expect is not None,'supply output or expectation')
    r=verify(a.root)
    if a.expect is not None:need(exact(r,json.loads(a.expect.read_text())),'receipt mismatch')
    if a.output is not None:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print('PASS: conditional period/width criteria; compiler-history occurrence UNPROVED')
if __name__=='__main__':main()
