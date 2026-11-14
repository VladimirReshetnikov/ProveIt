#!/usr/bin/env python3
"""Exact action-graph novelty with designated-start and broader cosmetic tests.

Usage: python3 check_novelty.py --reference-dir representatives --output result.json candidate.tm ...
Reference files may use native labels; every graph-spanning start is compared.
Bit complementation is deliberately a broader structural test: it is not an
all-zero-blank semantic equivalence. Halt writes and moves are suppressed for
the strongest test. Full tuples are compared, not hash equality.
"""
import argparse,hashlib,json,pathlib

def parse(path):
 raw=path.read_bytes();rows={}
 for line in raw.decode().splitlines():
  line=line.strip()
  if not line or line.startswith(('#',';','//')):continue
  q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t));assert b in (0,1) and w in (0,1) and d in ('L','R');assert (q,b) not in rows;rows[q,b]=(w,d,t)
 states={q for q,b in rows};assert set(rows)=={(q,b) for q in states for b in (0,1)}
 halt=set(a[2] for a in rows.values())-states;assert len(halt)==1
 return rows,states,next(iter(halt)),hashlib.sha256(raw).hexdigest()

def rooted(data,root,reflect=False,complement=False,loose=False):
 rows,states,halt,_=data;idx={root:0};todo=[root];out=[]
 for q in todo:
  row=[]
  for bit in (0,1):
   w,d,t=rows[q,bit^complement]
   if t==halt:
    row.append((0,'R',-1) if loose else (w^complement,('R' if d=='L' else 'L') if reflect else d,-1));continue
   if t not in idx:idx[t]=len(todo);todo.append(t)
   row.append((w^complement,('R' if d=='L' else 'L') if reflect else d,idx[t]))
  out.append(tuple(row))
 return tuple(out) if len(todo)==len(states) else None

def broad(data):
 best=None;wit=None
 for r,b in [(False,False),(True,False),(False,True),(True,True)]:
  for q in sorted(data[1]):
   x=rooted(data,q,r,b,True)
   if x is not None and (best is None or x<best):best=x;wit=(q,r,b)
 return best,wit

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--reference-dir',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('candidates',type=pathlib.Path,nargs='+');a=p.parse_args()
 candidates=[(path,parse(path)) for path in a.candidates];counts={len(d[1]) for _,d in candidates};refs=[];excluded=[]
 for path in sorted(a.reference_dir.glob('*.tm')):
  d=parse(path)
  if len(d[1]) not in counts:continue
  c,w=broad(d)
  if c is None:excluded.append(str(path));continue
  refs.append((path,d,c,w))
 results=[]
 for path,d in candidates:
  c,w=broad(d);assert c is not None
  # all candidates supplied here are dense with designated start zero.
  assert d[1]==set(range(len(d[1])))
  r0=rooted(d,0);assert r0 is not None
  matches=[str(p) for p,_,k,_ in refs if c==k]
  results.append({'candidate':str(path),'candidate_sha256':d[3],'working_states':len(d[1]),'transition_rows':len(d[0]),'start':0,'halt':d[2],
                  'rooted_fingerprint':hashlib.sha256(repr(r0).encode()).hexdigest(),'broad_cosmetic_fingerprint':hashlib.sha256(repr(c).encode()).hexdigest(),'canonical_witness':w,
                  'compared_reference_classes':len(refs),'matches':matches,'distinct_from_all_references':not matches})
 result={'comparison':'full canonical tuple equality','transformations':['arbitrary state renaming','any spanning root','global left/right reflection','global bit complementation','ignore halt-edge write/move'],
         'reference_inputs':[{'file':p.name,'sha256':d[3]} for p,d,_,_ in refs],'excluded_nonspanning':excluded,'results':results}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='reference_inputs'},indent=2))
if __name__=='__main__':main()
