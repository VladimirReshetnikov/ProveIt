#!/usr/bin/env python3
"""Twelve-positive-variable norm with h_old=q+h and W=I*(T+I).

Depends on the adjacent compact emitter and its unchanged upstream base.
The new proof justifies h_old>q on canonical compiler witnesses.
"""
from copy import deepcopy
from pathlib import Path
import json
import random
import build_compact_norm12 as compact

base=compact.base
HERE=Path(__file__).resolve().parent


def construct():
    packets=compact.construct()
    for p in packets:
        src=[]
        for row in p['source']:
            n=row[0]
            if n in ('hE','index0','kI'):continue
            if n=='Nk':
                src += [['h_old','+','q','h'],['hE','*','h_old','E'],['index0','-','k','hE']]
            if n=='TkI':row=['TkI','+','T','I']
            src.append(row)
        p['source']=src
        p['name']=p['name'].replace('compact_norm12','shifted_norm12')
        p['weight']='I*(T+I)'
        p['index_coordinate']='h_old=q+h; positivity is immediate, and the inverse shift is positive on all old compiler solutions.'
        if 'exact_degree' in p:p['exact_degree']=1097 if p['output']=='polynomial' else 2176
        else:p['residual_exact_degrees']=[7,2,1088]
        compact.audit(p)
    return packets


def leading_check(product,prime,seed):
    rng=random.Random(seed)
    lead={n:(1,rng.randrange(1,prime)) for n in product['witnesses']}
    lead.update({n:(0,c) for n,c in zip(product['fixed_numerals'],[31,127,10,45])})
    original=deepcopy(lead)
    for n,op,a,b in product['source']:
        da,ca=(0,a%prime) if isinstance(a,int) else lead[a]
        db,cb=(0,b%prime) if isinstance(b,int) else lead[b]
        if op=='*':lead[n]=(da+db,ca*cb%prime)
        else:
            d=max(da,db)
            lead[n]=(d,((ca if da==d else 0)+(cb if db==d else 0)*(1 if op=='+' else -1))%prime)
    get=lambda n:original[n][1]
    q=get('beta')*get('J')%prime;k=(get('eta')+get('zeta'))%prime
    expected=pow(2,64,prime)
    for x,power in [(get('i'),48),(k,112),(get('w'),80),(get('s'),192),(q,656)]:
        expected=expected*pow(x,power,prime)%prime
    assert lead['N']==(1088,expected) and expected
    etop=get('w')*get('s')*pow(q,4,prime)%prime
    nt=get('w')*(q-get('F')-get('alpha'))-get('z')*q
    expected_product=-expected*(q+get('h'))*etop*nt%prime
    assert lead['polynomial']==(1097,expected_product) and expected_product
    return {'prime':prime,'seed':seed,'norm':lead['N'],'product':lead['polynomial']}


def main():
    if not __debug__:raise RuntimeError('Do not run with -O.')
    ps=construct();shifted,product,sos,system,residual,sos_old=ps
    assert [p['ledger']['operations'] for p in ps]==[110,116,118,111,112,119]
    rng=random.Random(1097116)
    for _ in range(48):
        vals={n:rng.randrange(-3,5) for n in base.WITNESSES+base.FIXED}
        a=base.evaluate(product,vals)
        assert a['N']==base.independent_norm(a)
        assert a['N1']%8==0 and (a['N']-a['N0']**2)%64==0
        assert a['polynomial']==a['Nk']*a['Nt']*(1+a['N'])-1
        sh=base.evaluate(shifted,vals)
        old=base.evaluate(residual,dict(vals,z=vals['z']+1))
        assert sh['trans0']-sh['transport_rhs']==old['Nt']-1
        assert sh['Nk']==old['Nk'] and sh['N00']-sh['GN11']==old['N']
        so=base.evaluate(sos,vals)
        assert so['sos']==(old['Nk']-1)**2+(old['Nt']-1)**2+old['N']**2
    leads=[leading_check(product,p,s) for p,s in [(1000000007,1201),(1000000009,1202),(998244353,1203)]]
    receipt={'packets':[{k:p[k] for k in ['name','ledger']} for p in ps],
        'exact_signed_norm_fixtures':48,'coordinate_shift_fixtures':48,
        'leading_form_checks':leads,
        'scope':'Finite algebra and operation counts; canonical h_old>q is established mathematically in SHIFTED_NORM12_PROOF.md.'}
    for p in ps:(HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    (HERE/'SHIFTED_NORM12_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
