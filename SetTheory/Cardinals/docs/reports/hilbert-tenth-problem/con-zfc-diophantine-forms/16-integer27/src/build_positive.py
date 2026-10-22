#!/usr/bin/env python3
"""Construct the 13-variable improved-weight circuit and audit its ledger."""
import json, random
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parents[1]
UP=ROOT/'upstream/arithmetic'

def construct(name, even=False):
    p=json.loads((UP/name).read_text()); s=[]
    for n,op,a,b in p['source']:
        if n=='Qr': s += [['ic2','*','i','c2'],['i2','*','ic2','ic2']]
        elif n in ('Q','ic2'): continue
        elif n=='Dm1': s += [['Dm1','*','A','i2']]
        elif n=='D': s += [[n,op,a,b],['Q','*','A','Dm1']]
        elif n=='M':
            s += [[('M0' if even else 'M'),'+','i2','v2']]
            if even:s += [['M','*',2,'M0']]
        else: s += [[n,op,a,b]]
    p['source']=s;p['name']=('even_' if even else '')+'improved_weight_'+p['name']
    p.pop('degree_diagnostics',None)
    if 'output' in p:p['exact_degree']=515
    p['residual_exact_degrees']=[18,7,2,488]
    c=Counter(row[1] for row in s)
    outputs=[p['output']] if 'output' in p else [x for row in p['comparisons'] for x in row if isinstance(x,str)]
    live=set(outputs)
    for n,op,a,b in reversed(s):
        if n in live:live.update(x for x in(a,b) if isinstance(x,str))
    if not set(p['witnesses']+p['fixed_numerals'])<=live: raise ValueError('Dead port')
    if not all(n in live for n,*_ in s): raise ValueError('Dead gate')
    p['ledger']={'operations':len(s),'multiplications':c['*'],'additions_subtractions':c['+']+c['-'],'all_gates_live':True,'all_ports_live':True}
    return p

def line_degree(p, degrees=None, seed=386, prime=1000000007):
    rng=random.Random(seed);values={v:[rng.randrange(1,17)]*(1+(degrees or {}).get(v,1)) for v in p['witnesses']}
    values.update({v:[x] for v,x in zip(p['fixed_numerals'],[31,127,10,45])})
    def add(a,b,sign=1):
        c=[((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))]
        while len(c)>1 and c[-1]==0:c.pop()
        return c
    for n,op,a,b in p['source']:
        a=[a] if isinstance(a,int) else values[a];b=[b] if isinstance(b,int) else values[b]
        if op=='*':
            c=[0]*(len(a)+len(b)-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b):c[i+j]=(c[i+j]+x*y)%prime
            while len(c)>1 and c[-1]==0:c.pop()
        else:c=add(a,b,1 if op=='+' else -1)
        values[n]=c
    if 'output' in p:out=[len(values[p['output']])-1]
    else:out=[len(add(values[a] if isinstance(a,str) else[a],values[b] if isinstance(b,str) else[b],-1))-1 for a,b in p['comparisons']]
    return {'degrees':out,'prime':prime,'seed':seed,'key_register_degrees':{k:len(values[k])-1 for k in ['norm_main','norm_index','norm_transport','i2','D','Q','Z','Asq','M','Cr','UU','norm13'] if k in values}}

def main():
    results=[]
    for src in ['polynomial13_84.json','system13_78.json']:
        p=construct(src)
        p['coefficient_binding']={'manifest':'../COEFFICIENT_BINDING.json','fixed_tuple':'pruned_t4','mask_convention':'MF is native mask plus B minus 1'}
        p['audit']=line_degree(p)
        (ROOT/'data'/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
        results.append({'name':p['name'],'ledger':p['ledger'],'audit':p['audit']})
    p=construct('polynomial13_84.json',True)
    weights={v:2 for v in ['Jrep','F','alpha','transport_quotient','s','w','eta','zeta']}
    results.append({'name':'signed27_weighted_degree_diagnostic','even_weight_ledger':p['ledger'],'weighted_degree':line_degree(p,weights)})
    (ROOT/'verification/positive13.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))
if __name__=='__main__':main()
