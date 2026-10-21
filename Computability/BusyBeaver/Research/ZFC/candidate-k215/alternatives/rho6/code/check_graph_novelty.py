#!/usr/bin/env python3
"""Compare rooted deterministic binary tables under state renaming and symmetries.
This is an exact finite graph test, not semantic inequivalence of computations.
"""
import argparse,hashlib,json
from pathlib import Path

def read(p):
 T={};start=None
 for line in p.read_text().splitlines():
  if line.startswith('#! start '):start=int(line[9:]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert b in(0,1)and w in(0,1)and d in('L','R');assert(q,b)not in T;T[q,b]=(w,d,z)
 qs={q for q,b in T};assert start in qs;assert set(T)=={(q,b)for q in qs for b in(0,1)}
 ends={z for w,d,z in T.values()}-qs;assert len(ends)==1
 return T,start,ends.pop()
def canon(m,flip=False,mirror=False):
 T,start,halt=m;todo=[start];idx={start:0};out=[]
 for q in todo:
  rr=[]
  for bit in (0,1):
   w,d,z=T[q,bit^flip];w^=flip
   if mirror:d='R'if d=='L'else'L'
   if z==halt:k=-1
   else:
    if z not in idx:idx[z]=len(todo);todo.append(z)
    k=idx[z]
   rr.append([w,d,k])
  out.append(rr)
 assert len(todo)==len(T)//2,'Unreachable listed states cannot be ignored for this test'
 return json.dumps(out,separators=(',',':')).encode()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 m=read(a.candidate);n=len(m[0])//2;target=canon(m);tested=[];matches=[];unread=[];other=[]
 for p in sorted(a.root.rglob('*.tm')):
  try:r=read(p)
  except (ValueError,AssertionError,UnicodeDecodeError) as e:unread.append({'path':str(p.relative_to(a.root)),'error':type(e).__name__});continue
  if len(r[0])//2!=n:other.append(str(p.relative_to(a.root)));continue
  syms=[]
  try:
   for flip in (False,True):
    for mirror in (False,True):
     if canon(r,flip,mirror)==target:syms.append({'symbol_complement':flip,'left_right_mirror':mirror})
  except AssertionError:unread.append({'path':str(p.relative_to(a.root)),'error':'unreachable_listed_states'});continue
  tested.append({'path':str(p.relative_to(a.root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
  if syms:matches.append({'path':str(p.relative_to(a.root)),'symmetries':syms})
 result={'status':'NO_ISOMORPHIC_TABLE_IN_SCANNED_FAMILY'if not matches else'MATCHES_FOUND','candidate_sha256':hashlib.sha256(a.candidate.read_bytes()).hexdigest(),'working_states':n,'candidate_canonical_graph_sha256':hashlib.sha256(target).hexdigest(),'compared_tables':len(tested),'tested':tested,'matches':matches,'other_state_counts':len(other),'unparsed':unread,'scope':'Every .tm file in supplied root that uses complete five-column integer-labelled format and exactly this many graph-reachable states; start preserved, halt preserved, symbols optionally complemented, directions optionally mirrored. This does not claim no prior outside this corpus, nor computational inequivalence.'}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ('tested','unparsed')},indent=2))
if __name__=='__main__':main()
