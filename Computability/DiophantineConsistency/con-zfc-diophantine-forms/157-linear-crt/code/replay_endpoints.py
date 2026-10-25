#!/usr/bin/env python3
"""Regenerate final equations from frozen, exactly invertible certificates."""
from pathlib import Path
import argparse,json,sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'inherited/factorial_free/direct'))
import build_affine as producer
PROFILES=('P238','P239_sparse','P239_low_height')
def replay(stage,output):
    source=json.loads((stage/'equation.json').read_text())
    for profile in PROFILES:
        directory=ROOT/'equations'/profile
        certificate=json.loads((directory/'certificate.json').read_text())
        equation,expanded,metrics=producer.construct(source,certificate)
        # The public encoding is fixed independently of the producer's metadata.
        target={'schema':'sparse_integer_polynomial_v1','domain':'Z','variable_count':len(equation['variables']),
                'terms':expanded['terms']}
        metrics['row_support']=sum(len(row['terms']) for row in equation['residuals'])
        out=output/profile;out.mkdir(parents=True,exist_ok=True)
        for name,obj in [('equation.json',equation),('expanded_polynomial.json',target),('METRICS.json',metrics)]:
            (out/name).write_text(json.dumps(obj,sort_keys=True,indent=2)+'\n')
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('output',type=Path);p.add_argument('--stage',type=Path,default=ROOT/'source')
    args=p.parse_args();replay(args.stage,args.output)
