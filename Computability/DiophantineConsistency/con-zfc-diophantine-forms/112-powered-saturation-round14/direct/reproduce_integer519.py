#!/usr/bin/env python3
"""Reproduce the frozen 519-integer endpoint from its frozen raw input.

Example:
python reproduce_integer519.py --raw ../architecture/carrier_hybrid_shell/raw --output new-output
Only Python's standard library is required. The raw input is literal data;
no archived builder or downloaded program is executed.
"""
from pathlib import Path
import argparse,json
import build_signed as S
import factor_horn as F
import translate_coordinates as T
import terminal_elimination as E

def put(directory,name,obj):
    directory.mkdir(parents=True,exist_ok=True)
    (directory/name).write_bytes(E.canonical_bytes(obj))

def main():
    p=argparse.ArgumentParser();p.add_argument('--raw',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    if a.output.exists() and any(a.output.iterdir()):raise ValueError('output must be absent or empty')
    S.build(a.raw,a.output/'signed',16,True)
    guarded=json.loads((a.output/'signed/guarded.json').read_text())
    factored,fc=F.transform(guarded);projected,pc,metrics=E.optimize(factored,max_support=16);check=E.verify(factored,projected,pc)
    for name,obj in [('factored_source.json',factored),('factorization_certificate.json',fc),('equation.json',projected),('projection_certificate.json',pc),('expanded_polynomial.json',E.expand(projected)),('METRICS.json',metrics|check)]:put(a.output/'factored',name,obj)
    shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'] in ('t0','M0') or v['name'].endswith('minus1')}
    final=T.translate(projected,shifts);polynomial=E.expand(final)
    put(a.output/'final','equation.json',final);put(a.output/'final','expanded_polynomial.json',polynomial)
    print(json.dumps({'status':'PASS','variables':len(final['variables']),'rows':len(final['residuals']),'monomials':len(polynomial['terms']),'height':max(abs(c) for c,m in polynomial['terms'])},indent=2))
if __name__=='__main__':main()
