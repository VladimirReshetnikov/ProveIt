"""Replay the frozen residual basis reduction, preserving all pool rows."""
from pathlib import Path
import json,sys,copy
sys.path.insert(0,str(Path(__file__).parent/'upstream159/code'))
from reduce_radical import norm,terms,add,scale,mul,canonical,digest,metric

def build(parent,certificate,output):
    e=json.loads(Path(parent).read_text());c=json.loads(Path(certificate).read_text())
    if c['input_sha256']!=digest(e):raise ValueError('wrong input')
    rows=[norm(r['terms']) for r in e['residuals']]
    private={i for i,v in enumerate(e['variables']) if v.get('kind')=='pooled_power'}
    protected=sorted({j for j,r in enumerate(e['residuals']) if any(set(m)&private for a,m in r['terms'])})
    if len(protected)!=4:raise ValueError(('expected four pool rows',protected,private))
    if any(j in protected for i,j,k in c['operations']):raise ValueError('a pool row was used as a source')
    kept=[];omitted=[]
    for i,j,k in c['operations']:
        if i in protected:omitted.append([i,j,k]);continue
        rows[i]=add(rows[i],scale(rows[j],k));kept.append([i,j,k])
    out=copy.deepcopy(e);out['variant']+=':protected_integer_row_reduction'
    out['residuals']=[dict(r,terms=terms(p)) for r,p in zip(e['residuals'],rows)]
    cc={'schema':'integer_row_operations_v1','input_sha256':digest(e),'operations':kept,'output_sha256':digest(out)}
    meta={'protected_rows':protected,'protected_variables':sorted(private),'omitted_operations':omitted,'retained_operations':len(kept)}
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    poly=add(*(mul(p,p) for p in rows))
    for name,value in [('equation.json',out),('row_certificate.json',cc),('protection.json',meta),('metrics.json',metric(out,True)),('expanded_polynomial.json',{'schema':'sparse_integer_polynomial_v1','variables':len(out['variables']),'terms':terms(poly)})]:(output/name).write_bytes(canonical(value))
    print(meta,metric(out,True))
if __name__=='__main__':build(*sys.argv[1:])
