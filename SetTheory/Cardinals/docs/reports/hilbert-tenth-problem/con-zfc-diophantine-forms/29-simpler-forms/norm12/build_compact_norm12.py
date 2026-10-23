#!/usr/bin/env python3
"""Compact twelve-positive-variable norm derived from ProveIt package 21.

New separation weight: Bnd=I*(T+k*I), I=i*c^2.
Run beside the unchanged package-21 build_norm12.py supplied as provenance.
All arithmetic checks use Python's standard library. They check formulas
and operation counts, not the inherited compiler or ZFC consistency.
"""
from collections import Counter
from copy import deepcopy
from pathlib import Path
import json
import random
import build_norm12 as base

HERE = Path(__file__).resolve().parent


def audit(p):
    available=set(p['witnesses']+p['fixed_numerals'])
    deg={n:1 for n in p['witnesses']}
    deg.update({n:0 for n in p['fixed_numerals']})
    for n,op,a,b in p['source']:
        assert n not in available and op in ('+','-','*')
        assert all(isinstance(v,int) or v in available for v in (a,b))
        da=0 if isinstance(a,int) else deg[a]
        db=0 if isinstance(b,int) else deg[b]
        deg[n]=da+db if op=='*' else max(da,db)
        available.add(n)
    outputs=[p['output']] if 'output' in p else [v for c in p['comparisons'] for v in c if isinstance(v,str)]
    live=set(outputs)
    for n,_,a,b in reversed(p['source']):
        if n in live: live.update(v for v in (a,b) if isinstance(v,str))
    assert all(n in live for n,_,_,_ in p['source'])
    assert set(p['witnesses']+p['fixed_numerals'])<=live
    count=Counter(row[1] for row in p['source'])
    p['ledger']={'operations':len(p['source']), 'multiplications':count['*'],
        'additions_subtractions':count['+']+count['-'],
        'all_gates_live':True,'all_ports_live':True,
        'syntactic_degree_upper_bounds':{n:deg[n] for n in outputs}}
    return deg


def construct():
    residual,product,sos_old=base.construct()
    replacement=[['kI','*','k','I'],['TkI','+','T','kI'],['Bnd','*','I','TkI']]
    for p in (residual,product,sos_old):
        source=[]
        for row in p['source']:
            if row[0]=='bound0': source.extend(deepcopy(replacement))
            elif row[0] not in ('bound1','Bnd'): source.append(row)
        p['source']=source
        p['coefficient_binding']='Bind all four ports as a whole to package 19 wang943-compact-5pow10: B=2^(5^10), beta=B-1, K0=K, MC=MC, MF=MF_source (shifted source mask).'
        p['weight']='I*(T+k*I)'
    residual.update(name='compact_norm12_residual_system',residual_exact_degrees=[7,2,1104])
    product.update(name='compact_norm12_product',exact_degree=1113)
    sos_old.update(name='compact_norm12_sos_unshifted',exact_degree=2208)
    system=deepcopy(residual)
    system['source']=[row for row in system['source'] if row[0]!='N']
    system.update(name='compact_norm12_system111',comparisons=[['Nk',1],['Nt',1],['N00','GN11']])
    shifted=deepcopy(system)
    shifted['source']=[row for row in shifted['source'] if row[0] not in ('trans1','Nt')]
    j=next(i for i,row in enumerate(shifted['source']) if row[0]=='trans2')+1
    shifted['source'].insert(j,['transport_rhs','+','F','trans2'])
    shifted.update(name='compact_norm12_system110',comparisons=[['Nk',1],['trans0','transport_rhs'],['N00','GN11']],
        coordinate_convention='z_old=z+1 compared with the product; all supplied unknowns remain strictly positive.')
    sos=deepcopy(shifted)
    sos['source'] += [['rk','-','Nk',1],['rt','-','trans0','transport_rhs'],['rn','-','N00','GN11'],
        ['rk2','*','rk','rk'],['rt2','*','rt','rt'],['rn2','*','rn','rn'],
        ['sum0','+','rk2','rt2'],['sos','+','sum0','rn2']]
    sos.update(name='compact_norm12_sos118',output='sos',exact_degree=2208)
    sos.pop('comparisons');sos.pop('residual_exact_degrees')
    packets=[shifted,product,sos,system,residual,sos_old]
    for p in packets:audit(p)
    return packets


def leading_form_check(p,prime,seed):
    rng=random.Random(seed)
    leading={n:(1,rng.randrange(1,prime)) for n in p['witnesses']}
    leading.update({n:(0,c) for n,c in zip(p['fixed_numerals'],[31,127,10,45])})
    original=deepcopy(leading)
    for n,op,a,b in p['source']:
        da,ca=(0,a%prime) if isinstance(a,int) else leading[a]
        db,cb=(0,b%prime) if isinstance(b,int) else leading[b]
        if op=='*': leading[n]=(da+db,ca*cb%prime)
        else:
            d=max(da,db)
            c=((ca if da==d else 0)+(cb if db==d else 0)*(1 if op=='+' else -1))%prime
            leading[n]=(d,c)
    val=lambda n:original[n][1]
    q=val('beta')*val('J')%prime;k=(val('eta')+val('zeta'))%prime
    expected=pow(2,64,prime)
    for value,power in [(val('i'),48),(k,128),(val('w'),80),(val('s'),192),(q,656)]:
        expected=expected*pow(value,power,prime)%prime
    assert leading['N']==(1104,expected) and expected
    expected_product=expected*(-val('h')*val('w')*val('s')*pow(q,4,prime))%prime
    expected_product=expected_product*(val('w')*(q-val('F')-val('alpha'))-val('z')*q)%prime
    assert leading['polynomial']==(1113,expected_product) and expected_product
    return {'prime':prime,'seed':seed,'norm':leading['N'],'product':leading['polynomial']}


def main():
    if not __debug__:raise RuntimeError('Do not run with -O: verification uses assertions.')
    ps=construct();shifted,product,sos,system,residual,sos_old=ps
    assert [p['ledger']['operations'] for p in ps]==[110,116,118,111,112,119]
    rng=random.Random(1113116)
    for _ in range(48):
        v={n:rng.randrange(-3,5) for n in base.WITNESSES+base.FIXED}
        a=base.evaluate(product,v)
        assert a['N']==base.independent_norm(a)
        assert a['N1']%8==0 and (a['N']-a['N0']**2)%64==0
        assert a['polynomial']==a['Nk']*a['Nt']*(1+a['N'])-1
        sh=base.evaluate(shifted,v);v_old=dict(v,z=v['z']+1)
        old=base.evaluate(residual,v_old)
        assert sh['trans0']-sh['transport_rhs']==old['Nt']-1
        assert sh['Nk']==old['Nk'] and sh['N00']-sh['GN11']==old['N']
        so=base.evaluate(sos,v)
        assert so['sos']==(old['Nk']-1)**2+(old['Nt']-1)**2+old['N']**2
    lead=[leading_form_check(product,p,s) for p,s in [(1000000007,1201),(1000000009,1202),(998244353,1203)]]
    receipt={'packets':[{k:p[k] for k in ['name','ledger']} for p in ps],
        'exact_signed_norm_fixtures':48,'coordinate_shift_fixtures':48,
        'guard_modulus':64,'leading_form_checks':lead,
        'scope':'Finite algebra, shift, parity, liveness and leading-coefficient checks; semantic equivalence uses the mathematical proof and inherited compiler.'}
    for p in ps:(HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    (HERE/'COMPACT_NORM12_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
