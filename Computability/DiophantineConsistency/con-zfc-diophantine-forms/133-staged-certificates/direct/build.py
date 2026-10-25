#!/usr/bin/env python3
"""Rebuild the four delivered quartics, using Python's standard library only.

Writes only to the explicitly supplied output directory. The default is a
new temporary directory. No network, installs, subprocesses or proof search.
"""
from pathlib import Path
import argparse,hashlib,json,shutil,tempfile
import builder

HERE=Path(__file__).resolve().parent
PRESETS={
 'principal239':{'support_cap':20,'protected_variables':[169,94]},
 'sparse240':{'support_cap':20,'protected_variables':[169,180,94]},
 'minimum237':{'support_cap':20,'protected_variables':[]},
 'small_support255':{'support_cap':16,'protected_variables':[],'coefficient_limit':16},
}


def build(out):
 out=Path(out)
 if out.exists() and any(out.iterdir()):raise ValueError('Output directory must be empty')
 out.mkdir(parents=True,exist_ok=True)
 with tempfile.TemporaryDirectory(prefix='staged-cap-source-') as td:
  base=Path(td)/'source'
  builder.generate(base,support_cap=20,staged=True)
  raw=json.loads((base/'raw/equation.json').read_text())
  expected={169:'shared.W',180:'index_cap.Y',94:'mul.329'}
  for i,name in expected.items():
   if raw['variables'][i]['name']!=name:raise ValueError('Protected variable changed identity')
  summaries={}
  original=builder.h.psd.nonnegative_certificate
  for name,spec in PRESETS.items():
   if spec.get('coefficient_limit'):
    limit=spec['coefficient_limit']
    def bounded(poly):
     return None if max(abs(c) for c in poly.values())>limit else original(poly)
    builder.h.psd.nonnegative_certificate=bounded
   try:
    target,cert,poly=builder.h.psd.contract(raw,support_cap=spec['support_cap'],protected_variables=spec['protected_variables'])
   finally:builder.h.psd.nonnegative_certificate=original
   receipt,independent=builder.h.check.verify(raw,target,cert)
   if poly['terms']!=independent:raise ValueError('Independent coefficient mismatch')
   dest=out/name
   shutil.copytree(base/'raw',dest/'raw')
   for fn,obj in [('equation.json',target),('elimination_certificate.json',cert),('expanded_polynomial.json',poly),('VERIFICATION.json',receipt)]:builder.h.write(dest/'natural'/fn,obj)
   recipe={'name':name,'source':'common raw/equation.json','projection':spec,'metrics':receipt}
   builder.h.write(dest/'RECIPE.json',recipe)
   summaries[name]=recipe
  builder.h.write(out/'RESULTS.json',summaries)
 return summaries


if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
 a=p.parse_args();print(json.dumps(build(a.output),indent=2))
