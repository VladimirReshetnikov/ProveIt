#!/usr/bin/env python3
"""Check the exact closed-subtree deletion, primitive word, and redirected CFG.

This checks the source transformation only. The deleted push's arithmetic
contract and the modified proof compiler are ordinary proofs in the report.
"""
from pathlib import Path
import argparse,hashlib,json,sys
PINS={'baseline':'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9','candidate':'86ca1b05c5bfada9d77ece84b88a165a7d61fe3dd8623273d94d1e81f87ac8e3','source_language':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f'}
def sha(raw):return hashlib.sha256(raw).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--portable',type=Path,required=True);p.add_argument('--baseline',type=Path,required=True);p.add_argument('--candidate',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Assertions must be enabled')
 assert sha((a.portable/'source_language.py').read_bytes())==PINS['source_language']
 sys.path.insert(0,str(a.portable));import source_language as s
 oldraw,newraw=a.baseline.read_bytes(),a.candidate.read_bytes();assert sha(oldraw)==PINS['baseline'];assert sha(newraw)==PINS['candidate']
 oldrows,newrows=json.loads(oldraw),json.loads(newraw);old,new=s.tree(oldrows),s.tree(newrows)
 assert new==s.replace(old,'11111',s.subtree(old,'111111'))
 deleted=s.subtree(old,'111110');assert s.boundary(deleted)==(0,0,False)
 lo,hi=4718,4737
 oldword=[x[1:]for x in oldrows];newword=[x[1:]for x in newrows]
 assert oldword[:lo]+oldword[hi:]==newword
 og=s.graph_arithmetic(oldrows)[0];ng=s.graph_arithmetic(newrows)[0]
 assert og==s.graph_intervals(oldrows);assert ng==s.graph_intervals(newrows)
 def target(t):
  if lo<=t<hi:
   assert t==lo,('Non-entry edge into deleted closed block',t)
   t=hi
  return t-(hi-lo)if t>=hi else t
 edges=0
 for i,(effect,targets)in enumerate(og):
  if lo<=i<hi:continue
  j=i if i<lo else i-(hi-lo)
  assert ng[j][0]==effect
  assert tuple(ng[j][1])==tuple(target(t)for t in targets),(i,targets,ng[j])
  edges+=len(targets)
 receipt={'status':'EXACT_CLOSED_MACRO_DELETION_AND_CFG_PASS','baseline_sha256':sha(oldraw),'candidate_sha256':sha(newraw),'deleted_prefix':'111110','replaced_parent_prefix':'11111','retained_child_prefix':'111111','deleted_ordinal_interval':[lo,hi],'deleted_primitive_occurrences':hi-lo,'deleted_boundary':s.boundary(deleted),'candidate_metrics':s.metrics(new),'retained_cfg_edges_checked':edges,'scope':'Exact syntax, primitive word, and redirected control flow. The deleted arithmetic macro and modified enumerator calibration are ordinary proofs in formalism-checkpoint.tex; this is not proof-assistant verification.'}
 a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
