#!/usr/bin/env python3
"""Independently compare an explicit candidate TM with frozen corpus tables.

The strict comparison ignores state names and the initial root, but preserves
read/write symbols and directions. The broad comparison additionally permits
left/right reflection, global bit exchange, and arbitrary write/move on the
halting edge. Symbol exchange need not preserve a zero-blank computation.
Full canonical tuples are compared; SHA-256 is used only for identifiers.
"""
from pathlib import Path
import argparse,hashlib,json,sys
from census import parse_text,canonical_form,fingerprint

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('candidate',type=Path);ap.add_argument('--corpus',type=Path,default=Path(__file__).parent/'results/representatives');ap.add_argument('--output',type=Path);a=ap.parse_args()
 b=a.candidate.read_bytes();d=parse_text(b)
 if not d:raise ValueError('Candidate is not a complete binary L/R table with one halt')
 f=canonical_form(d);bf=canonical_form(d,True)
 if f is None:raise ValueError('Candidate has no spanning graph root; comparison not applicable')
 examined=[];strict=[];broad=[];disconnected=[]
 for p in sorted(a.corpus.glob('*.tm')):
  raw=p.read_bytes();x=parse_text(raw)
  if not x:raise ValueError(f'Unrecognized corpus table {p}')
  if len(x[1])!=len(d[1]):continue
  g=canonical_form(x)
  if g is None:disconnected.append(p.name);continue
  bg=canonical_form(x,True)
  examined.append({'file':p.name,'sha256':hashlib.sha256(raw).hexdigest(),'strict_graph':fingerprint(g),'broad_graph':fingerprint(bg)})
  if f==g:strict.append(p.name)
  if bf==bg:broad.append(p.name)
 result={'candidate':a.candidate.name,'candidate_sha256':hashlib.sha256(b).hexdigest(),'working_states':len(d[1]),'strict_graph':fingerprint(f),'broad_graph':fingerprint(bf),'strict_matches':strict,'broad_matches':broad,'spanning_graphs_checked':len(examined),'disconnected_diagnostics_excluded':disconnected,'comparisons_used_exact_tuples':True,'corpus_tables':examined,'scope_note':'Graph novelty alone proves neither semantic novelty nor a PA/iPRA consistency theorem.'}
 if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='corpus_tables'},indent=2))
if __name__=='__main__':main()
