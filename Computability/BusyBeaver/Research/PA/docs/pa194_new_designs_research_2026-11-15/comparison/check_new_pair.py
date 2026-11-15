#!/usr/bin/env python3
"""Explicit-bijection comparison and congruence audit of the two new machines."""
from pathlib import Path
import argparse,hashlib,json
import literal_inventory as lit
from novelty_check import match,spanning
from verify_corpus import congruence
def main():
 assert __debug__
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('mp',type=Path);ap.add_argument('lcsf3',type=Path);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 x=lit.parse_table(a.mp.read_bytes());y=lit.parse_table(a.lcsf3.read_bytes());assert x and y
 root=spanning(x);assert root is not None and spanning(y)is not None
 attempts=0;matches=[]
 for mirror,flip in[(False,False),(True,False),(False,True),(True,True)]:
  for q in sorted(y[1]):
   attempts+=1
   if match(x,root,y,q,mirror,flip)is not None:matches.append(dict(root=q,mirror=mirror,flip=flip))
 classes=[congruence(*x),congruence(*y)];assert attempts==776 and not matches and classes==[194,194]
 r=dict(status='PASS',mp_dense_sha256=hashlib.sha256(a.mp.read_bytes()).hexdigest(),lcsf3_dense_sha256=hashlib.sha256(a.lcsf3.read_bytes()).hexdigest(),rooted_comparisons=attempts,matches=matches,distinct=True,immediate_action_congruence_classes={'MP':classes[0],'LCSF3':classes[1]},scope='Arbitrary state bijections and roots, reflection, global symbol complement, erased terminal-entry actions. Symbol exchange is a structural screen.')
 a.output.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
