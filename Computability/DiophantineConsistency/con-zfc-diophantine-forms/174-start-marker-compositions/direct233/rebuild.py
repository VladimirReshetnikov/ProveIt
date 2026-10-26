#!/usr/bin/env python3
"""Reconstruct all three final coefficient artifacts from frozen certificates."""
from pathlib import Path
import copy,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import audit_projection as A
from verify import replace_all

def read(p):return json.loads(p.read_text())
def write(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(A.canonical(x))
if len(sys.argv)!=2:raise SystemExit('Usage: python3 -B rebuild.py OUTPUT_DIRECTORY')
destination=Path(sys.argv[1]).resolve()
if destination==ROOT or ROOT in destination.parents:raise ValueError('Choose an output directory outside the sealed package')
source=read(ROOT/'source/power239.json');eq=copy.deepcopy(source)
eq['residuals'][0]['terms']=A.serial({(3,):-1,(4,):1})
eq['residuals'][173]['terms']=A.serial({():-2,(101,):1,(236,):-4})
keep=[i for i in range(239)if i not in(4,101)];ren={i:j for j,i in enumerate(keep)}
eq['variables']=[source['variables'][i]for i in keep];eq['variant']='linear_power237';rows=[]
for i,row in enumerate(eq['residuals']):
    if i in(0,173):continue
    p=replace_all(A.polynomial(row['terms'],239),{4:{(3,):1},101:{():2,(236,):4}})
    rows.append(dict(row,terms=A.serial({tuple(ren[j]for j in m):c for m,c in p.items()})))
eq['residuals']=rows
for step in read(ROOT/'stages/radical234/projection_certificate.json')['steps']:eq=A.one_step(eq,step,numerical_controls=False)
radical=eq
affine=A.affine_projection(radical,read(ROOT/'stages/affine233/projection_certificate.json'))
summary={}
for name,parent in [('P233_balanced',affine),('P233_sparse',affine),('P234_sparse',radical)]:
    out=A.row_operations(parent,read(ROOT/'equations'/name/'row_certificate.json'))
    expansion=A.expanded_sos(out);metrics=A.metrics(out,expansion)
    files={'equation.json':out,'metrics.json':metrics,'expanded_polynomial.json':{'schema':'sparse_integer_polynomial_v1','variables':len(out['variables']),'terms':A.serial(expansion)}}
    for filename,data in files.items():
        if A.canonical(data)!=(ROOT/'equations'/name/filename).read_bytes():raise ValueError('Rebuilt bytes differ: '+name+'/'+filename)
        write(destination/name/filename,data)
    summary[name]=metrics
print(json.dumps(summary,indent=2))
