#!/usr/bin/env python3
"""Audit the 13-integer midpoint shift, without importing its builder."""
import gzip
import hashlib
import json
import math

from audit import Poly
from audit_norm_family import ROOT, PRIME, mod_eval, bound, require


def main():
    # Exact polynomial identity in independent formal variables H,Q,V.
    H,Q,V=[Poly.var(i) for i in range(3)]
    delta=Q-1
    radical=256*H*H*delta*(Q*V*V-1)
    L=8*H*(2*Q-1)*V
    K=64*H*H*V*V+256*H*H*delta
    require(not (L*L-radical-K).d,'universal midpoint identity')

    p=json.loads((ROOT/'parity13_shifted.json').read_text())
    old=json.loads((ROOT/'parity13_direct.json').read_text())
    kernel=json.loads((ROOT/'norm5_kernel.json').read_text())
    require(p['variables']==old['variables'],'unchanged quantified variables')
    require(p['fixed_numerals']==old['fixed_numerals'],'unchanged coefficients')
    require(p['polynomial_abbreviations'][-len(kernel['polynomial_abbreviations']):]==kernel['polynomial_abbreviations'],'exact audited generic norm kernel')
    norm_receipt=json.loads((ROOT/'NORM_FAMILY_AUDIT.json').read_text())
    require(norm_receipt['status']=='PASS','generic norm audit receipt')
    expanded=ROOT/'norm5_expanded.json'
    require(hashlib.sha256(expanded.read_bytes()).hexdigest()==norm_receipt['kernels']['5']['expanded_sha256'],'audited universal expansion')
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    ports={}
    for name,item in binding['ports'].items():
        raw=gzip.decompress((ROOT/'coefficients'/item['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==item['sha256_raw'],'coefficient '+name)
        ports[name]=int.from_bytes(raw,'little')%PRIME
    denv={key:0 for key in ports}
    denv.update({key:1 for key in p['variables']})
    for name,e in p['polynomial_abbreviations']:
        denv[name]=bound(e,denv)
    weights=[denv['rad'+str(i)]/2 for i in range(4)]
    require(weights==[23,7,28,15],'remaining radical weights')
    require(denv['Zbase']==7 and denv['Lshift']==59 and denv['Kshift']==58,'paired coefficient degrees')
    pair_bound=max(2*max([denv['Zbase']]+weights),
                   denv['Lshift']+max([denv['Zbase']]+weights),
                   denv['Kshift'])
    require(pair_bound==87 and 16*pair_bound==1392,'analytical upper bound')
    # The only degree-87 term in each conjugate is -2 L sqrt(rad2).
    require(weights.count(max(weights))==1 and max(weights)==28,'unique highest radical')
    require(59+28>2*28 and 59+28>58 and 59+28>59+23,'unique pair-factor leading term')
    values=[]
    cert=p['degree_certificate']
    for t in range(1393):
        env=dict(ports)
        env.update({name:slope*t%PRIME for name,slope in cert['slopes'].items()})
        for name,e in p['polynomial_abbreviations']:
            env[name]=mod_eval(e,env)
        require((env['Lshift']**2-env['rad4']-env['Kshift'])%PRIME==0,'literal specialization of midpoint identity')
        values.append(mod_eval(p['factored_residuals'][0],env))
    while len(values)>1:
        values=[(b-a)%PRIME for a,b in zip(values,values[1:])]
    leading=values[0]*pow(math.factorial(1392)%PRIME,-1,PRIME)%PRIME
    require(leading!=0 and leading==cert['leading_coefficient_mod_prime'],'exact full-DAG finite difference')
    predicted=pow(2,16,PRIME)*pow(cert['Lshift_leading_coefficient_mod_prime'],16,PRIME)*pow(cert['rad2_leading_coefficient_mod_prime'],8,PRIME)%PRIME
    require(predicted==leading,'factorwise leading coefficient agrees with full DAG')
    report={'status':'PASS','variables':13,'exact_degree':1392,
            'local_midpoint_identity':'exact polynomial identity over Z',
            'remaining_radical_weights':weights,'pair_factor_degree':87,'pair_factors':16,
            'leading_coefficient_mod_prime':leading,'prime':PRIME,
            'independent_full_DAG_finite_difference':'PASS',
            'integer_coordinate_change':'t_unshifted=t_shifted+4*(2Q-1)V',
            'source_semantics':'unchanged zero set by an integer-polynomial triangular shift'}
    (ROOT/'SHIFT_AUDIT.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__': main()
