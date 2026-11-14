#!/usr/bin/env python3
"""Exact finite comparison under renaming, any spanning start, reflection,
read/write symbol complementation, and irrelevant halting-edge actions.

Run: python3 -B verify_novelty.py CANDIDATE.tm [--start N]
The adjacent frontier_manifest.json and reference_tables/ fix the corpus.
"""
from pathlib import Path
import argparse,hashlib,json,sys
sys.dont_write_bytecode=True
from audit_corpus import parse,rooted
HERE=Path(__file__).resolve().parent

def canonical(data):
 p=parse(data)
 if p is None:raise ValueError('not a complete five-column numeric binary table')
 rows,states,start,halts=p
 if len(halts)!=1:raise ValueError('requires exactly one terminal halt label')
 signatures=[]
 for mirror in (False,True):
  for complement in (False,True):
   for q in states:
    t,n=rooted(rows,states,q,mirror,complement,True)
    if n==len(states):signatures.append(t)
 if not signatures:raise ValueError('no spanning root')
 return min(signatures)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('candidate',type=Path,nargs='?');ap.add_argument('--start',type=int);ap.add_argument('--output',type=Path);args=ap.parse_args()
 manifest=json.loads((HERE/'frontier_manifest.json').read_text());signatures={};records=[]
 for m in manifest:
  data=(HERE/m['file']).read_bytes()
  if hashlib.sha256(data).hexdigest()!=m['sha256']:raise ValueError('changed reference '+m['name'])
  sig=canonical(data)
  if sig in signatures:raise ValueError('two listed corpus entries are cosmetically equivalent: '+m['name']+' / '+signatures[sig])
  signatures[sig]=m['name'];records.append(dict(name=m['name'],sha256=m['sha256'],canonical_sha256=hashlib.sha256(json.dumps(sig,separators=(',',':')).encode()).hexdigest()))
 receipt=dict(frontier_tables=len(manifest),distinct_strong_graph_classes=len(signatures),equivalences_checked=['state renaming','every spanning root','left/right reflection','global read/write bit interchange','arbitrary write/move on halting edges'])
 if args.candidate:
  data=args.candidate.read_bytes();p=parse(data)
  if p is None:raise ValueError('invalid candidate')
  rows,states,start,halts=p
  if args.start is not None:start=args.start
  if start is None:raise ValueError('supply --start for native-labelled candidate')
  if start not in states:raise ValueError('start has no rows')
  sig=canonical(data);receipt['candidate']=dict(path=str(args.candidate),sha256=hashlib.sha256(data).hexdigest(),working_states=len(states),start=start,graph_reachable_states=rooted(rows,states,start)[1],halt_labels=sorted(halts),matches=signatures.get(sig),structurally_new=sig not in signatures)
 else:receipt['frontier']=records
 if args.output:args.output.write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
