#!/usr/bin/env python3
"""Deterministically rebuild both new literal polynomial circuits."""
from pathlib import Path
import json
from carrier14 import construct as degree26
from candidate14 import construct as degree30

HERE=Path(__file__).resolve().parent

def main():
    (HERE/'circuits').mkdir(exist_ok=True)
    rows=[]
    for name,make,degree,expected in [('p14_degree26',lambda:degree26(True,True),26,92),
                                     ('p14_degree30',lambda:degree30(True,False),30,85)]:
        data=make()
        data.update({'domain':'strictly positive integers','exact_total_degree':degree,
          'coefficient_binding':'../coefficients/COEFFICIENT_BINDING.json',
          'coefficient_aliases':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},
          'proof':'../proof.md'})
        if len(data['gates'])!=expected: raise ValueError('Operation count changed')
        (HERE/'circuits'/f'{name}.json').write_text(json.dumps(data,indent=2)+'\n')
        rows.append({'circuit':name,'positive_unknowns':len(data['variables']),
          'degree':degree,'operations':len(data['gates']),
          'operations_by_kind':{op:sum(g['op']==op for g in data['gates'])
                                  for op in ['add','sub','mul']}})
    (HERE/'METRICS.json').write_text(json.dumps(rows,indent=2)+'\n')
    print(json.dumps(rows,indent=2))

if __name__=='__main__': main()
