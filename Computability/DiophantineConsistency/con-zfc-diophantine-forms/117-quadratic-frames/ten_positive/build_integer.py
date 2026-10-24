#!/usr/bin/env python3
"""The explicit 30-integer, degree556 substitution companion."""
import argparse,json
from pathlib import Path
from collections import Counter
HERE=Path(__file__).resolve().parent

def build():
    p=json.loads((HERE/'equation.json').read_text());rows=[];witnesses=[]
    for j,x in enumerate(p['witnesses'],1):
        a,b,c=['int_'+str(j)+'_'+v for v in ['a','b','c']];witnesses += [a,b,c]
        prefix='positive_'+str(j)+'_'
        rows += [[prefix+'a2','*',a,a],[prefix+'b2','*',b,b],
          [prefix+'cp1','+',c,1],[prefix+'ccp1','*',c,prefix+'cp1'],
          [prefix+'ab','+',prefix+'a2',prefix+'b2'],
          [prefix+'abc','+',prefix+'ab',prefix+'ccp1'],[x,'+',prefix+'abc',1]]
    rows += p['source']
    return dict(name='integer30_positive_parametrization',domain='unrestricted integers',
      witnesses=witnesses,fixed_numerals=p['fixed_numerals'],source=rows,output='N',
      coefficient_binding=p['coefficient_binding'],operations=len(rows),
      operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=556,
      proof='Each old positive input equals 1+a^2+b^2+c(c+1); surjectivity by the three-square theorem. Degree doubles by the explicit nonzero leading product. This is a domain companion, not a new integer complexity record.')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
    p=build();data=(json.dumps(p,indent=2,sort_keys=True)+'\n').encode();path=HERE/'integer30.json'
    if args.check:
        if path.read_bytes()!=data:raise ValueError('integer companion mismatch')
    else:path.write_bytes(data)
    if p['operations']!=163 or p['operation_breakdown']!={'*':85,'+':62,'-':16}:raise ValueError('literal count')
    print(json.dumps({'status':'PASS','variables':30,'operations':163,'degree':556,'check':args.check}))
