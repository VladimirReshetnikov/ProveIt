#!/usr/bin/env python3
"""Exact evaluation at a supplied tuple, never a solvability decision."""
from pathlib import Path
import argparse,json,math

ROOT=Path(__file__).resolve().parents[1]


def evaluate(variant,point):
    counts={'natural234':234,'natural233':233,'integer702':702,'integer699':699}
    if variant not in counts:raise ValueError('unknown variant')
    if not isinstance(point,list) or len(point)!=counts[variant] or any(type(x) is not int for x in point):
        raise ValueError('expected a JSON array of exactly %d integers'%counts[variant])
    if variant.startswith('integer'):
        point=[point[i]**2+point[i+1]**2+point[i+2]*(point[i+2]+1)
               for i in range(0,len(point),3)]
    elif any(x<0 for x in point):
        raise ValueError('natural-domain coordinates must be nonnegative')
    eq=json.loads((ROOT/f'equations/natural{len(point)}/equation.json').read_text())
    residuals=[sum(c*math.prod(point[j] for j in m) for c,m in row['terms'])
               for row in eq['residuals']]
    result=sum(r*r for r in residuals)
    return {'variant':variant,'polynomial_value':result,'is_zero':result==0,
            'nonzero_residuals':sum(r!=0 for r in residuals)}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('point',type=Path)
    p.add_argument('--variant',choices=['natural234','natural233','integer702','integer699'],default='natural234')
    a=p.parse_args();print(json.dumps(evaluate(a.variant,json.loads(a.point.read_text())),indent=2))
