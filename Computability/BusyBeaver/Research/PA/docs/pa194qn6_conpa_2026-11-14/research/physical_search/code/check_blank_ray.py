#!/usr/bin/env python3
"""Check a literal blank prefix ending in an outward constant self-loop."""
from pathlib import Path
import argparse,hashlib,json
from check_qn6_quotient import parse
ROOT=Path(__file__).resolve().parents[1]
def check(path,start=74):
 rows=parse(path);q,h,ones=start,0,set();trace=[]
 for step in range(100001):
  assert(q,0)in rows,'The requested ray checker encountered a halt'
  bit=int(h in ones);w,d,n=rows[q,bit]
  exterior=not ones or(d==1 and h>max(ones))or(d==-1 and h<min(ones))
  if not bit and n==q and exterior:break
  assert step<100000,'No ray certified within the fixed prefix bound'
  trace.append([q,h,bit,w,d,n]);(ones.add if w else ones.discard)(h);q,h=n,h+d
 return {'table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'start':start,'steps':step,
  'final_state':q,'final_head':h,'one_cells':sorted(ones),'ray_action':list(rows[q,0]),
  'status':'RAY','trace':trace,'scope':'Exact literal blank prefix and outward self-loop; no consistency equivalence claimed.'}
if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('table',type=Path,nargs='?',default=ROOT/'inputs/relay193.native.tm');ap.add_argument('--output',type=Path);a=ap.parse_args();d=check(a.table)
 if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(d,indent=2)+'\n')
 print(json.dumps({k:v for k,v in d.items()if k!='trace'},indent=2))
