#!/usr/bin/env python3
"""Apply the 301 -> 88 runtime quotient to QN6 and certify its blank ray.

This is a rejection of the intended blank initialization, not an accepted
193-state consistency machine or an assertion of runtime correctness for QN6.
"""
from pathlib import Path
import argparse,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def parse(path):
 rows={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(n))
 return rows

def check(path):
 old=parse(path);assert len(old)==388
 assert old[88,0]==(0,1,122) and old[301,0]==(0,1,45) and old[51,0]==(0,1,16)
 rows={key:(w,d,88 if n==301 else n)for key,(w,d,n)in old.items()if key[0]!=301}
 rows[88,0]=(0,-1,51);rows[51,0]=(0,1,122)
 assert len(rows)==386 and {n for w,d,n in rows.values()}-{q for q,b in rows}=={254}
 q,h,ones=74,0,set();trace=[]
 for step in range(100001):
  if q==254:
   status='HALT';break
  bit=int(h in ones);w,d,n=rows[q,bit]
  if not bit and n==q and (not ones or (d==1 and h>max(ones))or(d==-1 and h<min(ones))):
   status='RAY';break
  if step==100000:status='OPEN';break
  trace.append([q,h,bit,w,d,n]);(ones.add if w else ones.discard)(h);q,h=n,h+d
 # The finite prefix and the outward self-loop certify the stated ray.
 assert status=='RAY'
 assert rows[q,0][2]==q and h not in ones
 return rows,{'input_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
  'working_states':193,'initial_state':74,'initial_head':0,'initial_ones':[],
  'status':status,'steps':step,'final_state':q,'final_head':h,'one_cells':sorted(ones),
  'ray_action':list(rows[q,0]),'trace':trace,'proof_scope':'Exact finite prefix followed by a constant outward blank self-loop; rejected blank initialization. No runtime refinement or consistency equivalence is claimed.'}

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--table',type=Path,default=ROOT/'inputs/qn6.native.tm');ap.add_argument('--output',type=Path);a=ap.parse_args()
 rows,receipt=check(a.table)
 if a.output:
  a.output.mkdir(parents=True,exist_ok=True)
  text=''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {n}\n'for(q,b),(w,d,n)in sorted(rows.items()))
  (a.output/'qn6_runtime193.native.tm').write_text(text)
  receipt['candidate_sha256']=hashlib.sha256(text.encode()).hexdigest()
  (a.output/'qn6_runtime193_blank.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
