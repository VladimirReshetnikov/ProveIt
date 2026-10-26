#!/usr/bin/env python3
"""Evaluate the exact fixed polynomial, optionally modulo a supplied integer."""
from pathlib import Path
import argparse,json,gzip
ROOT=Path(__file__).resolve().parent
def evaluate(values,modulus=None):
 e=json.loads((ROOT/'equation.json').read_text())
 if len(values)!=10 or any(type(x) is not int for x in values):raise ValueError('Supply exactly ten integers in the printed input order')
 if modulus is not None and modulus<=1:raise ValueError('Modulus must exceed one')
 env=dict(zip(e['witnesses'],values))
 for name,meta in e['coefficient_binding']['ports'].items():
  env[name]=int.from_bytes(gzip.decompress((ROOT/e['coefficient_binding']['path']/meta['file']).read_bytes()),'little')
 if modulus:env={k:v%modulus for k,v in env.items()}
 for name,op,a,b in e['source']:
  av=a if isinstance(a,int) else env[a];bv=b if isinstance(b,int) else env[b]
  env[name]=av+bv if op=='+' else av-bv if op=='-' else av*bv
  if modulus:env[name]%=modulus
 return env[e['output']]
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('values',help='JSON list of ten integers');ap.add_argument('--modulus',type=int)
 a=ap.parse_args();value=evaluate(json.loads(Path(a.values).read_text()),a.modulus)
 import sys
 if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
 print(value)
