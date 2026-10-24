#!/usr/bin/env python3
"""Unimodular integral translations, with literal coefficient reconstruction."""
from pathlib import Path
import argparse,copy,hashlib,json
import terminal_elimination as E

def translate(e,shifts):
    out=copy.deepcopy(e);out.pop('metrics',None);out.pop('elimination',None)
    for r in out['residuals']:
        p=E.normalize(r['terms'])
        for v,s in shifts.items():p=E.substitute(p,v,{(v,):1,():s})
        r['terms']=E.as_terms(p)
    out['variant']+=':integral_translation'
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('output',type=Path);args=ap.parse_args()
    e=json.loads(args.input.read_text());shifts={}
    for i,v in enumerate(e['variables']):
        n=v['name']
        if n.startswith('crt.encoded') or n in ('t0','M0') or n.endswith('minus1'):shifts[i]=-1
    out=translate(e,shifts);expanded=E.expand(out)
    metrics={'variables':len(out['variables']),'rows':len(out['residuals']),'degree':max(len(m) for c,m in expanded['terms']),
      'monomials':len(expanded['terms']),'height':max(abs(c) for c,m in expanded['terms']),
      'row_height':max(abs(c) for r in out['residuals'] for c,m in r['terms'])}
    cert={'schema':'integral_translation_v1','input_sha256':hashlib.sha256(E.canonical_bytes(e)).hexdigest(),'shifts':[[i,s] for i,s in sorted(shifts.items())],
          'convention':'old_coordinate = new_coordinate + shift','inverse':'new_coordinate = old_coordinate - shift',
          'output_sha256':hashlib.sha256(E.canonical_bytes(out)).hexdigest()}
    args.output.mkdir(parents=True,exist_ok=True)
    for n,x in [('equation.json',out),('expanded_polynomial.json',expanded),('translation_certificate.json',cert),('METRICS.json',metrics)]:
        (args.output/n).write_bytes(E.canonical_bytes(x))
    print(json.dumps(metrics,indent=2))
if __name__=='__main__':main()
