#!/usr/bin/env python3
"""Build a literal d=3 fixed-register-time quadratic schema; initial scratch is zero."""
from pathlib import Path
import argparse,json
from quadratic_core import semantic_table,compile_schema
R=Path(__file__).resolve().parent
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--steps',type=int,default=1);ap.add_argument('--output',type=Path)
    a=ap.parse_args();table=semantic_table(json.loads((R/'virtual3.json').read_text()))
    p=compile_schema(table,a.steps,initial=['L','R',0]);out=a.output or R/f'quadratic_schema_T{a.steps}.json'
    out.write_text(json.dumps(p,separators=(',',':'))+'\n')
    (R/'semantic_branches.json').write_text(json.dumps(table,separators=(',',':'))+'\n')
    print(json.dumps({'output':str(out),**p['ledger']},indent=2))
