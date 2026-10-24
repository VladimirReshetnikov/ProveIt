#!/usr/bin/env python3
"""Standard domain conversions, with no new frontier claim."""
import json
from pathlib import Path
from collections import Counter

ROOT=Path(__file__).resolve().parent

def convert(packet,domain):
    rows=[];mapping={};variables=[]
    def gate(op,x,y):
        n='lift_'+str(len(rows));rows.append([n,op,x,y]);return n
    for v in packet['witnesses']:
        if domain=='natural':
            u=v+'_nat';variables.append(u);mapping[v]=gate('+',u,1)
        else:
            a,b,c=[v+'_'+s for s in ('a','b','c')];variables.extend([a,b,c])
            # 1+a^2+b^2+c(c+1) ranges over precisely the positive integers.
            mapping[v]=gate('+',gate('+',gate('+',gate('*',a,a),gate('*',b,b)),gate('*',c,gate('+',c,1))),1)
    for name,op,a,b in packet['source']:
        rows.append([name,op,mapping.get(a,a),mapping.get(b,b)])
    p=dict(packet);p.update(name=packet['name']+'_'+domain,witnesses=variables,source=rows,
        domain='nonnegative integers' if domain=='natural' else 'unrestricted integers',
        operations=len(rows),operation_breakdown=dict(Counter(r[1] for r in rows)),
        exact_degree=packet['exact_degree']*(1 if domain=='natural' else 2),
        residual_degrees=[x*(1 if domain=='natural' else 2) for x in packet['residual_degrees']],
        system_operations=packet['system_operations']+len(rows)-len(packet['source']),
        parent_circuit='positive12_product.json',
        conversion='x=n+1' if domain=='natural' else 'x=1+a^2+b^2+c(c+1); Legendre three-square theorem',
        comparison_status='standard domain companion, not an improved unrestricted-integer frontier')
    return p

if __name__=='__main__':
    parent=json.loads((ROOT/'circuits/positive12_product.json').read_text())
    for domain in ['natural','integer']:
        p=convert(parent,domain)
        (ROOT/'circuits'/('natural12.json' if domain=='natural' else 'integer36.json')).write_text(json.dumps(p,indent=2)+'\n')
        print(json.dumps({k:p[k] for k in ('name','domain','operations','exact_degree')}))
