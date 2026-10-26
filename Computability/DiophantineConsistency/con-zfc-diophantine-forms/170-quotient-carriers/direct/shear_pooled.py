#!/usr/bin/env python3
"""Apply six attributed unimodular coordinate shears to the pooled source."""
from pathlib import Path
import sys,json,copy
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'inherited_radical'))
import reduce_radical as p
SHEARS=[['mul.40',{'crt.encoded.a':-2,'crt.encoded.b':-2}],
 ['mul.53',{'add.50':-8}],['mul.148',{'add.145':-8}],
 ['mul.137',{'crt.encoded.a':-4,'crt.encoded.c':-5,'mul.64':-2,'mul.75':-1}],
 ['mul.75',{'crt.encoded.a':-1,'crt.encoded.c':-1}],
 ['mul.64',{'crt.encoded.b':-1,'crt.encoded.c':-1}]]

def main():
 source=ROOT/'pooled225_radical/equation.json'
 eq=json.loads(source.read_text());new=copy.deepcopy(eq)
 names={v['name']:i for i,v in enumerate(eq['variables'])}
 rows=[p.norm(r['terms']) for r in eq['residuals']]
 ops=[]
 for target,inputs in SHEARS:
  t=names[target];subs=p.add(p.V(t),{(names[name],):c for name,c in inputs.items()})
  rows=[p.subst(r,{t:subs}) for r in rows]
  ops.append([t,[[names[name],c] for name,c in inputs.items()]])
 new['variant']+=':integral_coordinate_shears'
 new['residuals']=[dict(row,terms=p.terms(poly)) for row,poly in zip(eq['residuals'],rows)]
 out=ROOT/'pooled220_sheared';out.mkdir(exist_ok=True)
 cert={'schema':'integral_coordinate_shears_v1','source':'pooled225_radical/equation.json','input_sha256':p.digest(eq),'output_sha256':p.digest(new),'operations':ops,'attribution':'The same six shears supplied in Factorial-Free Binomial CRT direct/build_affine.py; no new semantic restriction.'}
 exp=p.add(*(p.mul(row,row) for row in rows))
 for name,data in {'equation.json':new,'shear_certificate.json':cert,'metrics.json':p.metric(new,True),'expanded_polynomial.json':{'schema':'sparse_integer_polynomial_v1','variables':len(eq['variables']),'terms':p.terms(exp)}}.items():(out/name).write_bytes(p.canonical(data))
 print(p.metric(new,True))

if __name__=='__main__':main()
