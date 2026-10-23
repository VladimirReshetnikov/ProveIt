#!/usr/bin/env python3
"""Independent full-degree and scalar-norm diagnostics for optional translation."""
import json
import random
from pathlib import Path
from build_eleven import WITNESSES,PORTS,evaluate
from build_eleven_translated import build_translated
from check_eleven import univariate,conjugate_norm

HERE=Path(__file__).resolve().parent

def need(x,message):
    if not x: raise AssertionError(message)

def main():
    packet=build_translated()
    receipt=[]
    for prime,seed in [(1000000007,43),(1000000009,47)]:
        rng=random.Random(seed)
        coeff={name:rng.randrange(1,20) for name in WITNESSES}
        coeff.update(dict(zip(PORTS,[31,127,10,45])))
        vals=univariate(packet,coeff,prime)
        q0=31*coeff['J'];k0=coeff['eta']+coeff['zeta'];s0=coeff['s']+3*q0
        lead=(2**46*coeff['i']**48*k0**96*coeff['w']**90*s0**188*q0**700*(q0-coeff['F'])**16)%prime
        transport=coeff['w']*(q0-coeff['F']-coeff['alpha'])-coeff['z']*q0
        need(lead and lead*transport%prime,'degenerate ray')
        need(vals['N']==(1138,lead),'unexpected full norm degree/leader: '+repr(vals['N']))
        need(vals['polynomial']==(1140,lead*transport%prime),'unexpected product degree/leader')
        receipt.append({'prime':prime,'norm':list(vals['N']),'product':list(vals['polynomial'])})
    rng=random.Random(1140129)
    for prime in [1000000007,1000000009]:
        for _ in range(30):
            assignment={name:rng.randrange(-7,8) for name in WITNESSES+PORTS}
            vals=evaluate(packet,assignment,prime)
            need(vals['N']==conjugate_norm(vals,prime),'translated norm mismatch')
    result={'full_univariate_degree_checks':receipt,'independent_modular_norm_cases':60,
            'ledgers':{kind:build_translated(kind)['ledger'] for kind in ['product','system','shifted_system']},
            'scope':'Finite algebra and degree diagnostics; positivity and completeness proved separately.'}
    (HERE/'generated'/'TRANSLATED_CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
