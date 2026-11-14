#!/usr/bin/env python3
"""Independently replay all finite prefixes and certify outward-ray continuations."""
from pathlib import Path
import argparse,json,hashlib
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
def table(path):
 d={}
 for line in path.read_text().splitlines():
  if not line.strip()or line.lstrip().startswith('#'):continue
  q,b,w,v,n=line.split();key=int(q),int(b);assert key not in d;d[key]=int(w),1 if v=='R'else -1,int(n)
 return d

def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
 assert __debug__
 src=ROOT/'candidate/machine/machine.native.tm';rows=table(src)
 assert hashlib.sha256(src.read_bytes()).hexdigest()=='424bd5175bbca161e76af485f1eda03f2f169d90afe80563035b60289361bf07'
 assert rows[88,0]==(0,1,122) and rows[301,0]==(0,1,45) and rows[51,0]==(0,1,16)
 rows={key:(w,d,88 if n==301 else n)for key,(w,d,n)in rows.items()if key[0]!=301}
 rows[88,0]=0,-1,51;rows[51,0]=0,1,122
 controls={q for q,b in rows};assert len(controls)==193 and len(rows)==386
 cert=json.loads((HERE/'new193_startup_rejection.json').read_text());records=cert['records'];assert len(records)==193 and {r['start']for r in records}==controls
 counts={};total=0
 for r in records:
  q=r['start'];head=0;ones=set()
  for item in r['trace']:
   bit=int(head in ones);w,d,n=rows[q,bit]
   assert item==[q,head,bit,w,d,n]
   (ones.add if w else ones.discard)(head);head+=d;q=n;total+=1
  assert len(r['trace'])==r['steps'] and(q,head,sorted(ones))==(r['q'],r['head'],r['ones'])
  if r['status']=='HALT':assert q not in controls
  elif r['status']=='RAY':
   assert head not in ones;w,d,n=rows[q,0]
   assert n==q and (not ones or(d==1 and head>max(ones))or(d==-1 and head<min(ones)))
   assert d==r['direction'] and w==r['write']
   # Induction: each future head is a previously blank exterior cell;
   # this same row moves farther outward and never reaches terminal.
  else:raise AssertionError('Unsupported or bounded classification: '+r['status'])
  counts[r['status']]=counts.get(r['status'],0)+1
 assert counts=={'HALT':2,'RAY':191}
 z=next(r for r in records if r['start']==74);assert(z['status'],z['steps'],z['q'],z['head'],z['ones'])==('RAY',92,35,14,[-3,1])
 result={'status':'PASS','working_states':193,'all_blank_starts':193,'classifications':counts,'literal_prefix_transitions_replayed':total,'max_prefix':max(r['steps']for r in records),'start74_prefix':92,'accepted_consistency_machine':False,'bounded_outcomes':0}
 if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
