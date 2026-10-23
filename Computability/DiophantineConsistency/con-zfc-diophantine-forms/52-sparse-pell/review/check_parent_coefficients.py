#!/usr/bin/env python3
"""Independent sparse expansion and fixed-height certificate for the parent.
This imports no upstream script; only the authenticated 60-gate JSON is read.
"""
from pathlib import Path
from collections import defaultdict
from hashlib import sha256
from math import factorial
import json

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
def require(c,m):
    if not c: raise ValueError(m)

def main():
    source=HERE/'sources/31-sun10/quartic31/quartic31_system60.json'
    data=json.loads(source.read_text())
    names=data['variables']+data['constants']
    n=len(data['variables']); size=len(names)
    zero=(0,)*size
    def unit(i): return tuple(int(j==i) for j in range(size))
    def add(a,b,sign=1):
        out=dict(a)
        for m,k in b.items():
            out[m]=out.get(m,0)+sign*k
            if out[m]==0: del out[m]
        return out
    def mul(a,b):
        out=defaultdict(int)
        for x,c in a.items():
            for y,d in b.items():out[tuple(u+v for u,v in zip(x,y))]+=c*d
        return {m:c for m,c in out.items() if c}
    env={name:({zero:1,unit(i):1} if i<n else {unit(i):1}) for i,name in enumerate(names)}
    def value(x):return {zero:x} if isinstance(x,int) and x else ({} if isinstance(x,int) else env[x])
    for out,op,left,right in data['source']:
        a,b=value(left),value(right)
        env[out]=add(a,b,1 if op=='+' else -1) if op in ('+','-') else mul(a,b)
    residuals=[add(value(a),value(b),-1) for a,b in data['comparisons']]
    binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text())
    ports={name:int.from_bytes((ROOT/'coefficients'/file).read_bytes(),'little') for name,file in [('beta','beta.bin'),('K0','K.bin'),('MC','MC.bin'),('MF','MF_source.bin')]}
    bits=[ports[name].bit_length() for name in data['constants']]
    rows=[]; maxU=maxWeighted=0
    for r,p in enumerate(residuals,1):
        grouped=defaultdict(dict)
        for m,c in p.items(): grouped[m[:n]][m[n:]]=c
        require(max(map(lambda m:sum(m),grouped))==2,'quadratic residual')
        for m,recipe in sorted(grouped.items()):
            U=sum(abs(c) << sum(e*b for e,b in zip(pe,bits)) for pe,c in recipe.items())
            exact=sum(c*__import__('functools').reduce(lambda a,v:a*v,(ports[name]**e for name,e in zip(data['constants'],pe)),1) for pe,c in recipe.items())
            weight=factorial(2-sum(m))
            for e in m:weight*=factorial(e)
            require(abs(exact)<=U,'triangle height bound')
            maxU=max(maxU,U); maxWeighted=max(maxWeighted,weight*U)
            rows.append({'residual':r,'variable_powers':list(m),'recipe':[{'port_powers':list(pe),'coefficient':c} for pe,c in sorted(recipe.items())],'factorial_weight':weight,'triangle_bound_bits':U.bit_length(),'exact_magnitude_bits':abs(exact).bit_length()})
    exponent=maxWeighted.bit_length()
    require(maxWeighted<1<<exponent,'strict coefficient majorant')
    # Common explicit overbound, suitable for the published direct source bounds.
    safe_exp=(4*33*33*maxU).bit_length()
    if safe_exp%2:safe_exp+=1
    require((1<<safe_exp)>4*33*33*maxU,'strict Sun source bound')
    record={'status':'PASS','scope':'Exact finite symbolic coefficient expansion and triangle bounds; not an unbounded solvability proof','parent_file':str(source.relative_to(ROOT)),'parent_sha256':sha256(source.read_bytes()).hexdigest(),'variables':data['variables'],'port_order':data['constants'],'port_bits':bits,'coherent_binding':'coefficients/COEFFICIENT_BINDING.json','positive_to_nonnegative_substitution':'each parent variable = corresponding nonnegative variable + 1','source_equations':len(residuals),'source_record_count':len(rows),'raw_coefficient_upper_bound_bits':maxU.bit_length(),'weighted_coefficient_upper_bound_bits':maxWeighted.bit_length(),'strict_weighted_majorant_exponent':exponent,'sun_even_source_multiplier_exponent':safe_exp,'sun_bound':'2^sun_even_source_multiplier_exponent > 4*33^2*max(raw symbolic triangle bounds)','records':rows}
    (ROOT/'coefficients/PARENT_COEFFICIENT_BOUND.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k!='records'},indent=2))

if __name__=='__main__':main()
