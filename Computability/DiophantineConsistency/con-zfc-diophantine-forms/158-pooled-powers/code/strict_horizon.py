"""Cofinal strict-bound reduction of Joint_Norm P245, standard library only."""
from pathlib import Path
from collections import defaultdict
import json, hashlib

def canonical(poly):
    return [[c,list(m)] for m,c in sorted(poly.items()) if c]

def recollect(rows):
    p=defaultdict(int)
    for row in rows:
        a=row['terms']
        for c,m in a:
            for d,n in a:
                p[tuple(sorted(m+n))]+=c*d
    return canonical(p)

def require(ok, detail='invalid reduction input'):
    if not ok: raise ValueError(detail)

def main(PARENT,OUT):
    OUT.mkdir(parents=True,exist_ok=True)
    raw=PARENT.read_bytes(); q=json.loads(raw)
    require(len(q['variables'])==245 and len(q['residuals'])==181)
    remove_vars={114,172,173,235}
    require({q['variables'][v]['name'] for v in remove_vars}=={'pow6.output','index_addition.D','pow6.quotient','remainder_budget.ratio1'})
    remove_rows={124,125,175}
    require(q['residuals'][175]['label']=='remainder_budget.ratio1')
    changed_range_rows=[93,94,95,96,103]
    # The removed power q^(t+1) has exactly the output, defining quotient,
    # and auxiliary Pell-discriminant wire identified below.
    uses={v:[i for i,r in enumerate(q['residuals']) if any(v in m for _,m in r['terms'])] for v in remove_vars}
    require(uses=={114:[125,159,175],172:[124,125],173:[125],235:[93,94,95,96,103,175]},str(uses))
    keep=[i for i in range(245) if i not in remove_vars]
    reindex={v:i for i,v in enumerate(keep)}
    rows=[]
    for i,r in enumerate(q['residuals']):
        if i in remove_rows: continue
        poly=defaultdict(int)
        for c,m in r['terms']:
            if i==159 and m==[114,114]:
                require(c==-1)
                continue
            if i in changed_range_rows:
                m=[234 if v==235 else v for v in m]
            require(not remove_vars.intersection(m),str((i,m)))
            poly[tuple(sorted(reindex[v] for v in m))]+=c
        rows.append({'label':r['label'],'terms':canonical(poly)})
    out={k:v for k,v in q.items() if k not in ['variables','residuals','variant','wire_eliminated_source_sha256']}
    out.update(variables=[q['variables'][i] for i in keep],residuals=rows,variant='cofinal_strict241',parent_sha256=hashlib.sha256(raw).hexdigest())
    expanded=recollect(rows)
    metrics=dict(variables=len(keep),rows=len(rows),degree=max(map(lambda x:len(x[1]),expanded)),monomials=len(expanded),height=max(abs(c) for c,_ in expanded),row_height=max(abs(c) for r in rows for c,_ in r['terms']))
    cert={'parent_sha256':hashlib.sha256(raw).hexdigest(),'removed_variables':sorted(remove_vars),'removed_rows':sorted(remove_rows),'range_rows_redirected':changed_range_rows,'ratio_redirection':{'from':235,'to':234},'removed_frame_term':[-1,[114,114]],'old_to_new':reindex,'uses':uses,'semantic_change':'All five schema/derived-label range lower indices t+1 become t. Choose cofinal horizon strictly greater than all finite witness parameters and labels.'}
    for name,data in [('equation241.json',out),('expanded241.json',expanded),('metrics241.json',metrics),('certificate241.json',cert)]:
        (OUT/name).write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps(metrics,indent=2))
if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();main(a.parent,a.output)
