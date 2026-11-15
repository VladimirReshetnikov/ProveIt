#!/usr/bin/env python3
"""Independent literal verification for the two accelerated variants.

The imported checker reconstructs list-sweep lemmas from the literal rows and
uses independent source resolvers; it imports no construction compiler.
"""
from pathlib import Path
import argparse,importlib.util
HERE=Path(__file__).resolve().parent
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--packet',type=Path,default=HERE.parent);ap.add_argument('--output',type=Path,default=HERE/'independent_results');args=ap.parse_args()
 spec=importlib.util.spec_from_file_location('parent_literal_checker',args.packet/'verification/check_literal.py')
 module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.EXPECTED.update({
  'dba0814631acf3f2db047d729b387fd929283186503a0e251139adfaf488c687':('PA194AX11GHF',3671,4778,57870),
  'd2d03d166c16367bf53c521ab572c24c91860e604b19cd247dd054275736b4d7':('PA194AX11GHSF',3668,4774,57712)})
 for family in('PA194AX11GHF','PA194AX11GHSF'):
  module.check(HERE/'machines'/family,args.output)
