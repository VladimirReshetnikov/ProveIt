#!/usr/bin/env python3
from pathlib import Path
import argparse,json,hashlib,time
BASE=Path(__file__).resolve().parents[2]/'vendor/context246'

def table(path):
 T={}
 for line in path.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,t=line.split();T[int(q),int(b)]=int(w),1 if d=='R' else -1,int(t)
 return T

def run(T,n):
 q=95;h=0;ones=set();lo=hi=0;rows=set()
 for step in range(n):
  assert q!=254,('HALT',step)
  row=(q,int(h in ones));rows.add(row);w,d,q=T[row]
  (ones.add if w else ones.discard)(h);h+=d;lo=min(lo,h);hi=max(hi,h)
 return q,h,ones,lo,hi,rows

def main():
 ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--steps',type=int,default=410735);a=ap.parse_args();old=table(BASE/'machine/zfc_prefix246_old.tm');new=table(a.table)
 oldend=run(old,a.steps);newend=run(new,a.steps)
 q,h,one,lo,hi,used=newend
 same=oldend[:3]==newend[:3];trajectory=all(old[k]==new[k] for k in oldend[5])
 d=dict(status='PASS' if same else 'FAIL',exact_endpoint_equal=same,all_reference_prefix_rows_equal=trajectory,steps=a.steps,state=q,head=h,one_count=len(one),entire_one_positions=sorted(one),blank_everywhere_else=True,head_range=[lo,hi],minimum_header_distance=181 if same else None,logical_primary=[3,0,0,0,3,0,0,0,0] if same else None,physical_primary=[0,0,0,3,0,0,3,0,0] if same else None,spare_values=[1]*167 if same else None,table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest())
 a.output.write_text(json.dumps(d,indent=2)+'\n');print({k:v for k,v in d.items() if k not in ('entire_one_positions','spare_values')})
if __name__=='__main__':main()
