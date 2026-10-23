#!/usr/bin/env python3
"""Independent ledger and leading-form audit of the supplied Hybrid12 circuits.

This checks finite algebraic evidence only. The unbounded argument is in
INDEPENDENT_HYBRID12_AUDIT.md. No imported builder is executed.
"""
from pathlib import Path
import json
import random

HERE=Path(__file__).resolve().parent
SRC=HERE.parent/'arithmetic'

def require(test,msg):
    if not test: raise ValueError(msg)

def top_values(packet,values):
    a={x:(1,values[x]) for x in packet['witnesses']}
    a.update({x:(0,values[x]) for x in packet['fixed_numerals']})
    for n,op,l,r in packet['source']:
        dl,cl=(0,l) if isinstance(l,int) else a[l]
        dr,cr=(0,r) if isinstance(r,int) else a[r]
        if op=='*': a[n]=(dl+dr,cl*cr)
        else:
            d=max(dl,dr)
            a[n]=(d,(cl if dl==d else 0)+(1 if op=='+' else -1)*(cr if dr==d else 0))
    return a

def ledger(packet):
    defined=set(packet['witnesses']+packet['fixed_numerals'])
    for n,op,l,r in packet['source']:
        require(n not in defined,'duplicate '+n)
        require(op in ('+','-','*'),'operator '+op)
        require(all(isinstance(x,int) or x in defined for x in (l,r)),'unknown input '+n)
        defined.add(n)
    outputs=[packet['output']] if 'output' in packet else [x for c in packet['comparisons'] for x in c if isinstance(x,str)]
    live=set(outputs)
    for n,_,l,r in reversed(packet['source']):
        require(n in live,'dead gate '+n)
        live.update(x for x in (l,r) if isinstance(x,str))
    require(set(packet['witnesses']+packet['fixed_numerals'])<=live,'unused input')
    return {'operations':len(packet['source']),'multiplications':sum(op=='*' for _,op,_,_ in packet['source']),
            'variables':len(packet['witnesses']),'all_gates_live':True}

def main():
    packets=[json.loads((SRC/f'hybrid12_square_unweighted_{kind}.json').read_text()) for kind in ('system','product','sos')]
    sizes=[ledger(p) for p in packets]
    require([x['operations'] for x in sizes]==[111,116,119],'sizes')
    require([x['multiplications'] for x in sizes]==[72,74,75],'multiply sizes')
    require(packets[0]['comparisons']==[['Nk',1],['Nt',1],['N00','GN11']],'system output')
    rng=random.Random(2026102207)
    count=32
    for _ in range(count):
        v={x:rng.randrange(1,8) for x in packets[1]['witnesses']}
        v.update(beta=rng.randrange(9,32),K0=137,MC=10,MF=45)
        p=top_values(packets[1],v)
        q=v['beta']*v['J'];k=v['eta']+v['zeta']
        nlead=2**32*v['i']**48*k**96*v['w']**80*v['s']**176*q**656*(q-v['F'])**16
        prodlead=-v['h']*v['w']*v['s']*q**4*(v['w']*(q-v['F']-v['alpha'])-v['z']*q)*nlead
        require(p['N']==(1072,nlead),'norm leading form')
        require(p['polynomial']==(1081,prodlead),'product leading form')
        require(p['GN11'][0]==1000,'other norm term degree')
        s=top_values(packets[2],v)
        require(s['sos']==(2144,nlead*nlead),'sos leading form')
    report={'status':'PASS','packets':sizes,'exact_leading_form_evaluations':count,
            'norm_degree':1072,'product_degree':1081,'sos_degree':2144,
            'uniform_proof':'The leading-form derivation is recorded separately, valid for every fixed beta>0.',
            'accounting_caution':'The direct-final-comparison rewrite also reduces package 21 system cost from 112 to 111; it is not an exclusive new operation-count record.'}
    (HERE/'HYBRID12_INDEPENDENT_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
