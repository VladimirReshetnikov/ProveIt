#!/usr/bin/env python3
"""Rebuild both literal quartics from the pinned raw source; standard library only."""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import build_linear_cofinal as producer

def build(output):
 output=Path(output)
 if output.exists() and any(output.iterdir()):raise ValueError('Output must be new or empty')
 summaries={}
 for name,staged,cap in [('natural235',False,40),('natural236_sparse',True,20)]:
  raw,trans=producer.transform(staged)
  target,cert,poly=producer.s.psd.contract(raw,support_cap=cap)
  receipt,terms=producer.s.check.verify(raw,target,cert)
  if terms!=poly['terms']:raise ValueError('Independent coefficient mismatch')
  dest=output/name
  for fn,obj in [('raw/equation.json',raw),('raw/transformation.json',trans),('equation.json',target),('elimination_certificate.json',cert),('expanded_polynomial.json',poly),('VERIFICATION.json',receipt)]:producer.s.write(dest/fn,obj)
  summaries[name]=target['metrics']
 producer.s.write(output/'RESULTS.json',summaries)
 return summaries
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();print(json.dumps(build(a.output),indent=2))
