#!/usr/bin/env python3
"""Reject three deliberately corrupted fold certificates with the real checker."""
from pathlib import Path
import argparse,copy,json
import check_seed_folds as f

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--parent',type=Path,required=True);ap.add_argument('--specification',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 t=f.read_table(a.parent);folds=json.loads(a.specification.read_text())['folds'];out=[]
 for name,change in [('wrong_scanned_tag',lambda fs:fs[0]['invariant']['118'].__setitem__('0',1)),('missing_support',lambda fs:fs[0]['invariant'].pop('159'))]:
  fs=copy.deepcopy(folds);change(fs)
  try:f.check_inductive_invariant(t,fs[0]['invariant'])
  except ValueError as e:out.append(dict(name=name,status='REJECTED',reason=str(e)))
  else:raise AssertionError(name+' incorrectly accepted')
 fs=copy.deepcopy(folds);fs[0]['a1']=[1,1,173]
 f.check_inductive_invariant(t,fs[0]['invariant']);nt,phi=f.transformed(t,fs[0]);w,d,z=t[185,1]
 try:f.local_block(nt,118,{0:1},(phi(z),d,{0:w}),16)
 except ValueError as e:out.append(dict(name='unreclaimed_read_one',status='REJECTED',reason=str(e)))
 else:raise AssertionError('Wrong transition accepted')
 a.output.write_text(json.dumps(out,indent=2)+'\n');print('THREE_INVALID_FOLD_CERTIFICATES_REJECTED')
if __name__=='__main__':main()
