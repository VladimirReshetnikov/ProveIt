#!/usr/bin/env python3
"""Exact cosmetic-equivalence check against all 34 supplied frontier graphs.

Comparisons use full canonical transition tuples; hashes are output labels,
not the equality test. Tests every graph-spanning root, reflection and bit
interchange, a stronger equivalence than fixed blank-start state renaming.
"""
import argparse,hashlib,json
from pathlib import Path

def read(path):
 rows={}
 for line in Path(path).read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'): continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  assert b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows
  rows[q,b]=(w,d,n)
 states={q for q,b in rows}
 assert len(rows)==2*len(states)
 assert len({n for w,d,n in rows.values()}-states)==1
 return rows,states

def canonical(rows,states):
 keys=[]
 for mirror,flip in ((False,False),(True,False),(False,True),(True,True)):
  for start in states:
   seen={start:0};order=[start];out=[]
   for q in order:
    for b in (0,1):
     w,d,n=rows[q,b^flip]
     if mirror:d='R' if d=='L' else 'L'
     if n in states:
      if n not in seen:seen[n]=len(seen);order.append(n)
      target=seen[n]
     else:target=-1
     out.append((w^flip,d,target))
   if len(seen)==len(states): keys.append(tuple(out))
 assert keys,'No spanning root; this comparator requires connected control graph'
 return min(keys)

def main():
 p=argparse.ArgumentParser();p.add_argument('candidate');p.add_argument('--output');a=p.parse_args()
 here=Path(__file__).resolve().parent
 rows,states=read(a.candidate);key=canonical(rows,states)
 data=json.loads((here/'frontier194_annotated.json').read_text());matches=[]
 for x in data:
  r,s=read(here/x['representative'])
  if len(s)==len(states) and canonical(r,s)==key:matches.append(x['name'])
 report={'candidate':str(Path(a.candidate).resolve()),'states':len(states),'corpus_frontier_graphs':len(data),
  'candidate_byte_sha256':hashlib.sha256(Path(a.candidate).read_bytes()).hexdigest(),
  'symmetry_key_sha256':hashlib.sha256(json.dumps(key,separators=(',',':')).encode()).hexdigest(),
  'matches':matches,'new_relative_to_this_frontier':not matches,
  'comparison':'Full tuples; arbitrary control renaming, spanning root, tape reflection and symbol interchange.'}
 text=json.dumps(report,indent=2)+'\n';print(text,end='')
 if a.output:Path(a.output).write_text(text)

if __name__=='__main__':main()
