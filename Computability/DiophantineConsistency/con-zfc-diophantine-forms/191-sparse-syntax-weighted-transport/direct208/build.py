#!/usr/bin/env python3
"""Rebuild all new mathematical artifacts from frozen finite inputs."""
from pathlib import Path
import argparse,contextlib,copy,hashlib,io,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'helpers'))
from polynomial import add,scale,mul,sub,const,var,poly,terms,subst,compact,expand,degree,canonical
import reduce_radical
import local_compiler
import export_equation

def save(folder,e,cert=None):
    folder.mkdir(parents=True,exist_ok=True)
    p=expand(e)
    metrics={'variables':len(e['variables']),'rows':len(e['residuals']),
             'degree':degree(p),'monomials':len(p),'height':max(map(abs,p.values())),
             'row_height':max(abs(c) for r in e['residuals'] for c,m in r['terms'])}
    files=[('equation.json',e),('metrics.json',metrics),
           ('expanded_polynomial.json',{'schema':'sparse-polynomial-v1','variables':len(e['variables']),'terms':terms(p)})]
    if cert is not None:files.append(('certificate.json',cert))
    for filename,data in files:(folder/filename).write_bytes(canonical(data))
    return metrics

def build(output):
    output.mkdir(parents=True,exist_ok=True)
    e,graft,_=local_compiler.generate('sparse')
    metrics={'local_sparse':save(output/'stages/local_sparse',e,graft)}
    before=copy.deepcopy(e);names={v['name']:i for i,v in enumerate(e['variables'])}
    index=next(j for j,r in enumerate(e['residuals']) if r['label']=='growth_pell.norm')
    X=var(names['growth_pell.X']);Z=var(names['growth_pell.tF']);F=var(names['growth.F'])
    original=e['residuals'][index]['terms']
    e['residuals'][index]['terms']=terms(add(mul(X,X),scale(-64,mul(Z,Z)),scale(-16,mul(Z,F)),const(-1)))
    e['growth_pell_center']='8*t+1';e['syntax']='I=4((a+b)^2+a),M=I+1,A=I+2,E=I+3'
    gc={'schema':'sparse-syntax-growth-change-v1','input_sha256':hashlib.sha256(canonical(before)).hexdigest(),
        'row':index,'before':original,'after':e['residuals'][index]['terms']}
    metrics['source214']=save(output/'stages/source214',e,gc)
    t,z=names['t0'],names['cofinal.horizon_root']
    h=next(j for j,r in enumerate(e['residuals']) if r['label']=='cofinal.horizon')
    parent_sha=hashlib.sha256(canonical(e)).hexdigest()
    e['residuals']=[dict(r,terms=terms(subst(poly(r['terms']),t,add(const(2),scale(4,var(z))))))
                    for j,r in enumerate(e['residuals']) if j!=h]
    e['variables'][z]['name']='horizon.affine_parameter';e,ren=compact(e)
    hc={'schema':'affine-horizon-projection-v1','input_sha256':parent_sha,'minimum':2,'old_t':t,'old_z':z,
        'deleted_row':h,'restore_t':terms(add(const(2),scale(4,var(ren[z])))),
        'renumbering':[[i,j] for i,j in ren.items()]}
    metrics['affine213']=save(output/'stages/affine213',e,hc)
    with contextlib.redirect_stdout(io.StringIO()):e,pc=reduce_radical.reduce(e)
    metrics['radical208']=save(output/'stages/radical208',e,pc)
    parent_sha=hashlib.sha256(canonical(e)).hexdigest()
    ops=json.loads((ROOT/'source/charts.json').read_bytes());rows=[poly(r['terms']) for r in e['residuals']]
    for op in ops:
        if op['type']=='coordinate':rows=[subst(r,op['coordinate'],poly(op['image'])) for r in rows]
        elif op['type']=='row':rows[op['target']]=add(rows[op['target']],scale(op['multiple'],rows[op['source']]))
        else:raise ValueError('Unknown integral operation')
    e['residuals']=[dict(r,terms=terms(p)) for r,p in zip(e['residuals'],rows)]
    cc={'schema':'elementary-integral-operations-v1','input_sha256':parent_sha,'operations':ops,
        'output_sha256':hashlib.sha256(canonical(e)).hexdigest()}
    metrics['principal208']=save(output/'equations/principal208',e,cc)
    export_equation.export(output/'equations/principal208')
    (output/'metrics.json').write_bytes(canonical(metrics))
    return metrics

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT)
    args=ap.parse_args();print(json.dumps(build(args.output.resolve()),sort_keys=True))
