#!/usr/bin/env python3
"""Independent formal-radical multiplication check for the new 11-variable norm."""
import importlib.util
import itertools
import json
from pathlib import Path
import random

ROOT=Path(__file__).resolve().parent
BUILD=ROOT.parent/'eleven/build.py'
spec=importlib.util.spec_from_file_location('eleven_builder',BUILD)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)

def require(condition,message):
    if not condition:raise ValueError(message)

def check():
    rand=random.Random(20261023)
    trials=0
    for prime in (1009,10007,1000000007):
        for carrier in ('midpoint','full'):
            circuit=module.build('product',carrier)
            for trial in range(12):
                inputs={x:rand.randrange(prime) for x in circuit['witnesses']+circuit['fixed_numerals']}
                env=module.evaluate(circuit,inputs,prime)
                rad=[env['G'],env['A'],env['D']]
                def add(a,b,scale=1):return [(x+scale*y)%prime for x,y in zip(a,b)]
                def constant(n):return [n%prime]+[0]*7
                def monomial(i,n):
                    v=[0]*8;v[i]=n%prime;return v
                def mul(a,b):
                    v=[0]*8
                    for ia,x in enumerate(a):
                        for ib,y in enumerate(b):
                            z=x*y
                            for bit in range(3):
                                if ia&ib&(1<<bit):z*=rad[bit]
                            v[ia^ib]=(v[ia^ib]+z)%prime
                    return v
                S=env['S'];W=env['W'];L=env['L'];d=env['d'];Q=env['Q']
                b=env['b'];v=env['v'];D=env['D']
                e=(Q*(D*v*v+b*b)-1)%prime;Baux=(2*Q*v*b)%prime
                result=constant(1)
                for sg,sa,sf in itertools.product((-1,1),repeat=3):
                    x=add(add(constant(W),monomial(1,-sg*L)),monomial(2,-sa*S))
                    fac=mul(constant(d),mul(x,x))
                    fac=add(fac,constant(-S*S*e))
                    fac=add(fac,monomial(4,sf*S*S*Baux))
                    result=mul(result,fac)
                require(result==constant(env['N']),f'formal norm mismatch {prime},{carrier},{trial}')
                require(env['N']%prime==(env['term2']-env['term1'])%prime,'norm sign')
                if carrier=='midpoint':
                    w=(env['U']*(env['b0']+env['H']*(inputs['t']+b+env['ell']))
                       +env['H']*(2*env['q4']*env['k']-env['residue']))%prime
                    require(w==W,'undoubled midpoint carrier')
                trials+=1
    receipt={'formal_radical_products':trials,'primes':[1009,10007,1000000007],
             'carriers':['midpoint','full'],'formal_signs_per_product':8,
             'result':'all passed','scope':'Finite implementation check only; no unbounded semantic claim.'}
    (ROOT/'midpoint_independent_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':check()
