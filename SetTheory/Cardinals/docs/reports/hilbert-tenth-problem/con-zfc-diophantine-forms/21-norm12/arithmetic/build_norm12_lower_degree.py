#!/usr/bin/env python3
"""Optional lower-degree 12-positive-variable variant; primary packets unchanged."""
from copy import deepcopy
from pathlib import Path
import json
import random
import build_norm12 as base

HERE=Path(__file__).resolve().parent


def construct():
    ps=base.construct()
    repl=[['TI','*','T','I'],['fourTI','*',4,'TI'],['asix','+','a',6],
          ['ic','*','i','c'],['i2c3','*','I','ic'],['Ra6','*','R','asix'],
          ['smallbound0','*','Ra6','i2c3'],['smallbound1','*',2,'smallbound0'],
          ['smallbound2','+','fourTI',2],['Bnd','+','smallbound1','smallbound2']]
    for p in ps:
        s=[]
        for row in p['source']:
            if row[0]=='bound0':s+=deepcopy(repl)
            elif row[0] not in ('bound1','Bnd'):s.append(row)
        p.update(name=p['name']+'_lower_degree',source=s)
        if 'output' in p:p['exact_degree']=1177 if p['output']=='polynomial' else 2336
        else:p['residual_exact_degrees']=[7,2,1168]
        base.ledger(p)
    return ps


def main():
    ps=construct();rng=random.Random(121177)
    for _ in range(24):
        vals={n:rng.randrange(-2,4) for n in base.WITNESSES+base.FIXED}
        a=base.evaluate(ps[0],vals)
        if a['N']!=base.independent_norm(a):raise ValueError('Lower-degree norm identity failure')
    receipt={'packets':[{k:p[k] for k in ['name','ledger']} for p in ps],
             'signed_exact_conjugate_product_fixtures':24,
             'scope':'Positive-domain variant only; no integer26 claim is attached to this weight.'}
    for p in ps:(HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    (HERE/'norm12_lower_degree_checks.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
