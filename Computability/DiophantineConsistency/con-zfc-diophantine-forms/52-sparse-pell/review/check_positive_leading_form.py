#!/usr/bin/env python3
"""Independent check of the new lean positive equation and its leading form.

The candidate is read only as a division-free JSON DAG. No candidate builder,
checker, or upstream executable is imported. Whole univariate polynomials are
evaluated, then compared with a separately transcribed analytic leading form.
"""
from pathlib import Path
from hashlib import sha256
import json
import numpy as np

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def check(c,m):
    if not c:raise ValueError(m)

def main():
    path=ROOT/'positive/positive11_Y_lean_product.json'
    data=json.loads(path.read_text())
    binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text())
    ports={a:int.from_bytes((ROOT/'coefficients'/(b+'.bin')).read_bytes(),'little') for a,b in binding['port_aliases'].items()}
    rows=[]
    for prime in (101,1009,65521):
        for trial in (1,2,3):
            scales={v:2+((i+3)*(trial+2))%23 for i,v in enumerate(data['witnesses'])}
            env={v:np.array([0,s],dtype=np.int64) for v,s in scales.items()}
            env.update({v:np.array([c%prime],dtype=np.int64) for v,c in ports.items()})
            def term(t):return env[t] if isinstance(t,str) else np.array([t%prime],dtype=np.int64)
            for name,op,left,right in data['source']:
                a,b=term(left),term(right)
                if op=='*': ans=np.convolve(a,b)%prime
                else:
                    ans=np.zeros(max(len(a),len(b)),dtype=np.int64)
                    ans[:len(a)]+=a
                    ans[:len(b)]+=b if op=='+' else -b
                    ans%=prime
                nz=np.flatnonzero(ans)
                env[name]=ans[:int(nz[-1])+1] if len(nz) else np.array([0],dtype=np.int64)
            v=scales
            q=ports['beta']%prime*v['J']%prime
            s=(v['s']+3*q)%prime
            X=v['w']*q%prime;Y=s*pow(q,3,prime)%prime;E=X*Y%prime
            k=(v['eta']+v['zeta'])%prime;c=k*Y%prime;I=v['i']*c*c%prime
            ell=E*c%prime;H=4*E%prime;d=pow(E,4,prime)*I*I%prime
            R=pow(q,3,prime)*(q-v['F'])%prime;B=R*E*E*I*I%prime
            V=I*v['T']*ell%prime
            check(E!=0,'specialization denominator')
            bracket=(2*v['t']-k-v['i']*v['T']*c*pow(E,-1,prime))%prime
            leading=pow(2,12,prime)*pow(H,16,prime)*pow(d,8,prime)*pow(B,8,prime)*pow(V,4,prime)*ell*ell*c*bracket%prime
            leading=leading*pow(Y,16,prime)%prime
            transport=(v['w']*(q-v['F']-v['alpha'])-v['z']*q)%prime
            norm=env['N'];product=env[data['output']]
            check(leading!=0 and transport!=0,'vanishing specialization')
            check(len(norm)-1==952 and int(norm[-1])==leading,'norm degree or predicted leading coefficient')
            check(len(product)-1==954 and int(product[-1])==leading*transport%prime,'product degree or predicted leading coefficient')
            rows.append({'prime':prime,'trial':trial,'norm_degree':len(norm)-1,'norm_leading_coefficient':int(norm[-1]),'predicted_norm_leading_coefficient':leading,'product_degree':len(product)-1,'product_leading_coefficient':int(product[-1]),'predicted_product_leading_coefficient':leading*transport%prime})
    result={'status':'PASS','candidate_sha256':sha256(path.read_bytes()).hexdigest(),'checks':rows,'scope':'Exact complete univariate computations validate the displayed multivariate leading-form specialization and give degree lower bounds; the ordinary Laurent-factor argument supplies the upper bound.'}
    (HERE/'POSITIVE_LEADING_FORM_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
