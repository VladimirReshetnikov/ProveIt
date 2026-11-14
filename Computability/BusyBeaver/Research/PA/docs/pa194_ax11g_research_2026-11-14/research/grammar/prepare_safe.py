#!/usr/bin/env python3
"""Recreate eleven templates from the admitted-ending pricing receipt."""
import argparse
from prepare import *
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--prices',type=Path,default=HERE/'recorded/safe_terminal/prices.json')
 p.add_argument('--output',type=Path)
 a=p.parse_args();out=output_dir(a.output,'ax11g-safe-templates-')
 data=json.loads(a.prices.read_text())
 variants=[('safe'+str(j),replace_last(G,tup(v['terminal'])))for j,v in enumerate(data)if v['price']<=194]
 assert len(variants)==11
 print(json.dumps(write_templates(variants,out,'safe_templates.txt',False),indent=2));print('output',out)
