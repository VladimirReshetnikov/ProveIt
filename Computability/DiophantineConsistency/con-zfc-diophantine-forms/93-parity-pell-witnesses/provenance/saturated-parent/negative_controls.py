#!/usr/bin/env python3
"""Reject two operation-preserving corruptions of the released literal DAG.

Controls operate on memory copies only. They never change the release packet.
"""
import copy
import json
from pathlib import Path
import verify

ROOT=Path(__file__).resolve().parent


def main():
    actual=verify.coefficients();results=[]
    for name in ('integer17_degree88','integer16_degree184'):
        packet=verify.read('equations/'+name+'.json')
        original=verify.read('circuits/'+name+'.json')
        corrupt=copy.deepcopy(original)
        # Swap the right operand of a genuine subtraction without changing
        # operation type/count or acyclicity. A valid earlier alternative is
        # chosen, and the exact term-algebra binding must reject it.
        target=next(i for i,n in enumerate(corrupt['nodes'])
                    if n['type']=='sub' and i>=2)
        node=corrupt['nodes'][target]
        node['right']=next(j for j in range(target) if j!=node['right'])
        try:
            verify.exact_degree_and_dag(packet,corrupt,actual)
        except ValueError as exc:
            verify.require('term-algebra' in str(exc),'corruption rejected for expected exact binding reason')
            results.append({'name':name,'corrupted_gate':target,'result':'rejected',
                            'reason':str(exc),'operation_count_unchanged':True})
        else:raise ValueError('corrupt literal circuit was accepted')
    receipt={'status':'PASS','controls':results,'release_files_modified':False}
    (ROOT/'certificates/NEGATIVE_CONTROLS.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
