#!/usr/bin/env python3
"""Select a sparse prefix of inherited exact integer row operations."""
from pathlib import Path
import sys,json,copy
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'inherited_radical'))
import reduce_radical as p

def select(n):
    source=ROOT/f'radical{n}'
    eq=json.loads((source/'equation.json').read_text())
    certificate=json.loads((ROOT/f'radical{n}_reduced/row_certificate.json').read_text())
    ops=certificate['operations']
    rows=[p.norm(r['terms']) for r in eq['residuals']]
    expansion=p.add(*(p.mul(r,r) for r in rows))
    best={}
    for k,op in enumerate([[0,1,0]]+ops):
        if k:
            i,j,a=op
            old=rows[i]
            rows[i]=p.add(old,p.scale(rows[j],a))
            expansion=p.add(expansion,p.scale(p.mul(old,old),-1),p.mul(rows[i],rows[i]))
        h=max(map(abs,expansion.values()))
        for limit in [4576,6144,7968,11232]:
            score=(len(expansion),h,k)
            if h<=limit and (limit not in best or score<best[limit][0]):
                best[limit]=(score,copy.deepcopy(rows),copy.deepcopy(expansion))
    census={}
    for limit,(score,rr,exp) in best.items():
        out=ROOT/f'radical{n}_height{limit}'
        out.mkdir(exist_ok=True)
        target=copy.deepcopy(eq)
        target['variant']+=':integer_row_reduction'
        target['residuals']=[dict(r,terms=p.terms(q)) for r,q in zip(eq['residuals'],rr)]
        cert={'schema':'integer_row_operations_v1','input_sha256':p.digest(eq),'operations':ops[:score[2]],'output_sha256':p.digest(target)}
        metrics=p.metric(target,True)
        files={'equation.json':target,'row_certificate.json':cert,'metrics.json':metrics,'expanded_polynomial.json':{'schema':'sparse_integer_polynomial_v1','variables':len(target['variables']),'terms':p.terms(exp)}}
        for name,data in files.items():(out/name).write_bytes(p.canonical(data))
        census[str(limit)]={'prefix_operations':score[2],**metrics}
    print(json.dumps({'source':n,'profiles':census},indent=2),flush=True)
    return census

if __name__=='__main__':
    census={str(n):select(n) for n in [238,239]}
    (ROOT/'RADICAL_PREFIX_CENSUS.json').write_text(json.dumps(census,indent=2,sort_keys=True)+'\n')
