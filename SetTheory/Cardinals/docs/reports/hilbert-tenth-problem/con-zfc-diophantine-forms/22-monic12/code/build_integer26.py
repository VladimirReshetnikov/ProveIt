#!/usr/bin/env python3
"""Emit and audit the 26-integer monic-merger circuit.

The semantic proof is integer26_proof.md. This program verifies only finite
algebra, exact circuit metrics and degree bounds/attainment. It never expands
the four astronomical compiler coefficients or searches for a K215 witness.
"""
import argparse
import copy
import json
import random
from collections import Counter
from pathlib import Path

POS = ['J', 'F', 'alpha', 'z', 's', 'eta', 'zeta']
FREE = ['h', 'T', 'u', 'i_integer', 'w_integer']


def prelude():
    source, names = [], []
    for v in POS:
        x,y,z = [v+'__'+a for a in ('x','y','z')]
        names += [x,y,z]
        source += [[v+'__x2','*',x,x],[v+'__y2','*',y,y],
                   [v+'__zp1','+',z,1],[v+'__tri','*',z,v+'__zp1'],
                   [v+'__twosq','+',v+'__x2',v+'__y2'],
                   [v+'__nonneg','+',v+'__twosq',v+'__tri'],
                   [v,'+',v+'__nonneg',1]]
    source += [['i_twice','*',2,'i_integer'],['i','+','i_twice',1],
               ['w','*','w_integer','w_integer']]
    return source,names+FREE


def evaluate(packet, values, prime=None):
    env=dict(values)
    for n,op,a,b in packet['source']:
        x=a if isinstance(a,int) else env[a]
        y=b if isinstance(b,int) else env[b]
        z=x+y if op=='+' else x-y if op=='-' else x*y
        env[n]=z if prime is None else z%prime
    return env


def ledger(packet):
    known=set(packet['witnesses']+packet['fixed_numerals'])
    for n,op,a,b in packet['source']:
        assert n not in known and op in ['+','-','*']
        assert all(isinstance(x,int) or x in known for x in [a,b])
        known.add(n)
    outputs=[packet['output']] if 'output' in packet else [
        x for row in packet['comparisons'] for x in row if isinstance(x,str)]
    need=set(outputs)
    for n,op,a,b in packet['source'][::-1]:
        if n in need: need.update(x for x in [a,b] if isinstance(x,str))
    assert all(row[0] in need for row in packet['source'])
    assert set(packet['witnesses']+packet['fixed_numerals'])<=need
    cnt=Counter(row[1] for row in packet['source'])
    return {'operations':len(packet['source']),'multiplications':cnt['*'],
            'additions_subtractions':cnt['+']+cnt['-'],
            'all_ports_live':True,'all_gates_live':True}


def degree_bounds(packet):
    env={x:1 for x in packet['witnesses']}
    env.update({x:0 for x in packet['fixed_numerals']})
    for n,op,a,b in packet['source']:
        x=0 if isinstance(a,int) else env[a]
        y=0 if isinstance(b,int) else env[b]
        env[n]=x+y if op=='*' else max(x,y)
    return env


def independent_horner(env, prime):
    """Independent pair evaluation of p^8 H8((W+sqrt(B))/p)."""
    B=env['B']
    def mul(x,y):
        return ((x[0]*y[0]+B*x[1]*y[1])%prime,
                (x[0]*y[1]+x[1]*y[0])%prime)
    inv=pow(env['p'],-1,prime)
    v=(env['W']*inv%prime,inv)
    v2=mul(v,v); v4=mul(v2,v2)
    d,N,e,a0=[env[x] for x in ['d','N','e','a0']]
    c2=-2*d*(N+e); c0=d*d*((N-e)**2+4*a0)
    q=((v4[0]+c2*v2[0]+c0)%prime,(v4[1]+c2*v2[1])%prime)
    r=((v2[0]+d*(N-e))%prime,v2[1])
    q2=mul(q,q);r2=mul(r,r)
    hz=((q2[0]-16*a0*d*d*r2[0])%prime,
        (q2[1]-16*a0*d*d*r2[1])%prime)
    scale=pow(env['p'],8,prime)
    real=hz[0]*scale%prime;imag=hz[1]*scale%prime
    return (real*real-B*imag*imag)%prime


def degree_specialization(packet, prime=1000000007):
    rng=random.Random(262993)
    env={x:[rng.randrange(1,20),rng.randrange(1,20)] for x in packet['witnesses']}
    env.update(dict(zip(packet['fixed_numerals'],[[31],[127],[10],[45]])))
    for n,op,a,b in packet['source']:
        x=[a] if isinstance(a,int) else env[a]
        y=[b] if isinstance(b,int) else env[b]
        if op=='*':
            z=[0]*(len(x)+len(y)-1)
            for j,xx in enumerate(x):
                for k,yy in enumerate(y): z[j+k]+=xx*yy
        else:
            z=[0]*max(len(x),len(y))
            for j,xx in enumerate(x): z[j]+=xx
            for j,yy in enumerate(y): z[j]+=yy if op=='+' else -yy
        z=[v%prime for v in z]
        while len(z)>1 and not z[-1]: z.pop()
        env[n]=z
    return {x:len(env[x])-1 for x in ['Nk','Nt','resultant','polynomial']}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source-file',type=Path,
                    default=Path(__file__).resolve().parents[1]/'data/merger12_product.json')
    ap.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parents[1]/'data')
    args=ap.parse_args();args.output_dir.mkdir(parents=True,exist_ok=True)
    base=json.loads(args.source_file.read_text())
    pre,names=prelude()
    assert len(pre)==52 and len(names)==26
    packet=copy.deepcopy(base)
    packet.pop('degree_upper_by_register',None)
    packet.update(name='integer26_product',witness_domain='unrestricted integers',
                  witnesses=names,source=pre+base['source'],exact_degree=2993,
                  substitution={'positive_ports':POS,'positive_map':'1+x^2+y^2+z(z+1)',
                                'free_ports':FREE,'i':'2*i_integer+1','w':'w_integer^2',
                                'additional_operations':52},
                  coefficient_contract='Use one whole authentic blank-native tuple beta,K0,MC,shifted MF; canonical width,height,base exponent must be powers of five.')
    packet['ledger']=ledger(packet)
    assert packet['ledger']['operations']==169
    bounds=degree_bounds(packet)
    assert [bounds[x] for x in ['Nk','Nt','resultant','polynomial']]==[13,4,2976,2993]
    packet['degree_upper_by_register']=bounds
    prime=1000000007;rng=random.Random(262026);checks=0
    while checks<150:
        values={x:rng.randrange(-8,9) for x in names}
        values.update(beta=31,K0=127,MC=10,MF=45)
        env=evaluate(packet,values,prime)
        if not env['p']:continue
        expected=independent_horner(env,prime)
        assert env['resultant']==expected
        assert env['polynomial']==(env['Nk']*env['Nt']*(1+expected)-1)%prime
        checks+=1
    # Check substitution against the supplied 12-coordinate source, in exact integers.
    for _ in range(30):
        values={x:rng.randrange(-2,3) for x in names}
        values.update(beta=15,K0=19,MC=2,MF=20)
        env=evaluate(packet,values)
        old={x:env[x] for x in base['witnesses']+base['fixed_numerals']}
        original=evaluate(base,old)
        assert env['polynomial']==original['polynomial']
        assert env['himag']%2==0
    attained=degree_specialization(packet)
    assert attained=={'Nk':13,'Nt':4,'resultant':2976,'polynomial':2993}
    system=copy.deepcopy(packet)
    system.pop('output');system.pop('exact_degree')
    # Compare the two norm squares directly, omitting their subtraction.
    assert packet['source'][-5]==['resultant','-','norm_real_square','B_norm_imag_square']
    system.update(name='integer26_system',source=packet['source'][:-5],
                  comparisons=[['Nk',1],['Nt',1],['norm_real_square','B_norm_imag_square']],
                  residual_exact_degrees=[13,4,2976],
                  max_equation_degree=2976)
    system['ledger']=ledger(system)
    assert system['ledger']['operations']==164
    # The removed finalizer's degree entries are not part of this system.
    system['degree_upper_by_register']={x:y for x,y in bounds.items()
                                       if x in set(system['witnesses']+system['fixed_numerals']+
                                                   [r[0] for r in system['source']])}
    for p in [packet,system]:
        (args.output_dir/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    receipt={'unknowns':26,'domain':'unrestricted integers',
             'product_ledger':packet['ledger'],'system_ledger':system['ledger'],
             'exact_product_degree':2993,'exact_system_degrees':[13,4,2976],
             'independent_pair_horner_checks':checks,'exact_substitution_checks':30,
             'modular_degree_witness':{'prime':prime,'seed':262993,'degrees':attained},
             'uniform_exact_degree_proof':'../proofs/integer26_proof.md',
             'semantic_status':'ordinary proof with inherited compiler/signed-core dependencies; not a new kernel theorem',
             'scope':'finite circuit/algebra audit; no giant coefficient expansion or K215 witness'}
    (args.output_dir/'audit_integer26.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__': main()

