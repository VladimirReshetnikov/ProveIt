#!/usr/bin/env python3
"""Independent finite checks subordinate to the all-natural arguments.

The evaluator implements structured composition directly, without the
source-CFG resolver or literal TM simulator used by the construction.
"""
from pathlib import Path
import argparse
import json
import random

ROOT=Path(__file__).resolve().parent

def evaluate(tree,a,b):
    regs={5:a,6:b};steps=0
    def ev(n):
        nonlocal steps
        steps+=1
        if steps>2000000:raise RuntimeError('finite diagnostic step cap')
        if isinstance(n[0],str):
            op,r=n
            if op=='CI':regs[r]+=1;return 'N',0
            if op=='CD':
                if not regs[r]:return 'B',1
                regs[r]-=1;return 'N',0
            if op=='CC':return 'C',r
            if op=='CB':return 'B',r
            raise ValueError(n)
        while True:
            kind,depth=ev(n[0])
            if kind=='B':return ('N',0)if depth==1 else ('B',depth-1)
            if kind!='N':return kind,depth
            kind,depth=ev(n[1])
            if kind=='C':
                if depth==1:continue
                return 'C',depth-1
            return kind,depth
    outcome=ev(tree)
    return outcome,regs[5],regs[6],steps

def check(output):
    tests=[(a,b)for a in range(64)for b in range(64)]
    rng=random.Random(218)
    tests += [(rng.randrange(10001),rng.randrange(10001))for _ in range(64)]
    tests += [(10000,10000),(0,10000),(10000,0),(9999,10000),(10000,9999)]
    summary={'status':'PASS_FINITE_ARITHMETIC','scope':'Finite diagnostics; all-natural arguments are in encoding_results.tex',
             'cases_per_macro':len(tests),'macros':[]}
    for name in ('asymmetric','strict_order'):
        macro=json.loads((ROOT/'macros'/f'{name}.json').read_text());total=maximum=0
        for a,b in tests:
            event,x,y,steps=evaluate(macro,a,b)
            if name=='asymmetric':expected=(('N',0)if a==b else ('B',1),0,max(b-a-1,0))
            else:expected=(('B',1)if a<b else ('N',0),0,0)
            assert (event,x,y)==expected,(name,a,b,event,x,y,expected)
            total+=steps;maximum=max(maximum,steps)
        summary['macros'].append({'name':name,'status':'PASS','total_evaluator_node_visits':total,
                                 'maximum_evaluator_node_visits':maximum})
    output=Path(output);output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(summary,indent=2)+'\n')
    return summary

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True)
    print(json.dumps(check(parser.parse_args().output),indent=2))
