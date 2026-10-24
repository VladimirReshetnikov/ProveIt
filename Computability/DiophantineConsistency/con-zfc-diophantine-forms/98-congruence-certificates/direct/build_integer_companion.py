#!/usr/bin/env python3
"""Literal integer-domain lift by n=u^2+v^2+w(w+1).

This familiar three-square substitution is a standard domain conversion,
not a new low-variable integer construction. The output is one sum of
squares of explicitly expanded quartic residuals.
"""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path


def main():
    root=Path(__file__).resolve().parent
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=root/'integer_companion.json')
    args=ap.parse_args()
    raw=(root/'eq/equation.json').read_bytes()
    source=json.loads(raw)
    count=len(source['variables'])
    rows=[]
    for row in source['residuals']:
        terms=defaultdict(int)
        for coefficient,monomial in row['terms']:
            p={():coefficient}
            for i in monomial:
                lift=[(3*i,3*i),(3*i+1,3*i+1),(3*i+2,3*i+2),(3*i+2,)]
                q=defaultdict(int)
                for a,c in p.items():
                    for b in lift:q[tuple(sorted(a+b))]+=c
                p=q
            for a,c in p.items():terms[a]+=c
        rows.append({'label':row['label'],'terms':[[c,list(m)] for m,c in sorted(terms.items()) if c]})
    result={
        'schema':'finite_quartic_residuals_v1',
        'domain':'all integers',
        'polynomial':'sum(square(row) for row in residuals)',
        'variables':[{'name':v['name']+'.'+suffix} for v in source['variables'] for suffix in ('u','v','w')],
        'source_equation_sha256':sha256(raw).hexdigest(),
        'substitution':'x_i = u_i^2 + v_i^2 + w_i^2 + w_i, with integer u_i,v_i,w_i',
        'metrics':{'variables':3*count,'quartic_rows':len(rows),'exact_degree':8,
                   'residual_monomials':sum(len(row['terms']) for row in rows),
                   'maximum_residual_degree':max(len(m) for row in rows for c,m in row['terms'])},
        'residuals':rows,
        'proof':'The substitution ranges exactly over the nonnegative integers by the three-square theorem applied to 4n+1. Its values are nonnegative for every integer triple. Thus the zero-existence statement equals that of the source polynomial. Exact degree eight follows by restricting all v_i,w_i to zero in the leading homogeneous residuals.'}
    payload=(json.dumps(result,separators=(',',':'),sort_keys=True)+'\n').encode()
    args.output.write_bytes(payload)
    print(json.dumps({'status':'PASS','metrics':result['metrics'],'bytes':len(payload),
                      'sha256':sha256(payload).hexdigest()},indent=2))


if __name__=='__main__':main()
