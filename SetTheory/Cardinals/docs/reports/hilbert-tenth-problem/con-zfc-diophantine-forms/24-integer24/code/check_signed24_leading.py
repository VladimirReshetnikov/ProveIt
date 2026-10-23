#!/usr/bin/env python3
"""Check the independently supplied signed24 leading-monomial certificate.
The formula itself is a uniform paper proof; these are full-polynomial
finite-field cross-checks, not a replacement for that proof.
"""
import gzip,json
from hashlib import sha256
from pathlib import Path
from degree_check import mul,add
HERE=Path(__file__).resolve().parent

def coefficient(packet,p,zswitch,coefficient_values=None):
    active=['J_x','h','ii','eta_x','ww','ss']
    if zswitch:active.append('z_x')
    vals={n:([0,1]if n in active else[0])for n in packet['witnesses']}
    fixed=coefficient_values or dict(beta=31,K0=127,MC=10,MF=45)
    vals.update({n:[fixed[n]%p]for n in packet['fixed_numerals']})
    for n,op,a,b in packet['source']:
        a=[a%p]if isinstance(a,int)else vals[a];b=[b%p]if isinstance(b,int)else vals[b]
        vals[n]=mul(a,b,p)if op=='*'else add(a,b,p,1 if op=='+'else-1)
    arr=vals[packet['output']]
    return arr[1936]if len(arr)>1936 else 0

def main():
    packet=json.loads((HERE.parent/'circuits'/'signed_separating_saturated24_product.json').read_text())
    binding=json.loads((HERE.parent/'coefficients/COEFFICIENT_BINDING.json').read_text())
    fixed={}
    for row in binding['files']:
        raw=gzip.decompress((HERE.parent/'coefficients'/row['file']).read_bytes())
        if sha256(raw).hexdigest()!=row['sha256']:raise ValueError('Coefficient digest mismatch')
        fixed[row['port']]=int.from_bytes(raw,'little')
    checks=[];C=255**4*(57599*73983)**2
    for p in[1000000007,1000000009]:
        a=coefficient(packet,p,False,fixed);b=coefficient(packet,p,True,fixed)
        found=(b-a)%p;expected=pow(2,257,p)*(C%p)*pow(fixed['beta']%p,677,p)%p
        if found!=expected:raise ValueError(('coefficient mismatch',p,found,expected))
        if found==0:raise ValueError('Leading coefficient vanished')
        checks.append({'prime':p,'coefficient_difference':found,'formula_mod_p':expected,'nonzero':found!=0,
                       'actual_coefficient_residues':{n:fixed[n]%p for n in packet['fixed_numerals']}})
    result={'status':'PASS','coefficient_formula':'2^257 * [255^4*(57599*73983)^2] * beta^677',
      'monomial':'J_x^1354*h*ii^48*eta_x^192*ww^162*ss^177*z_x^2',
      'total_degree':1936,'checks':checks,'coefficient_source':'complete actual materialized tuple',
      'scope':'Full finite-field evaluations support the separate uniform symbolic leading-form proof.'}
    (HERE.parent/'evidence'/'signed24_leading_certificate_checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
