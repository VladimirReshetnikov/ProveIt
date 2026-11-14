#!/usr/bin/env python3
"""Independent literal-tape check of the two positive contraction fixtures."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent

def read(path):
 ans={}
 for line in path.read_text().splitlines():
  q,b,w,d,n=line.split();ans[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(n))
 return ans

def run(rows):
 q,h,ones=0,0,set()
 for steps in range(20):
  if (q,0)not in rows:return q,h,tuple(sorted(ones)),steps
  w,d,q=rows[q,int(h in ones)]
  (ones.add if w else ones.discard)(h);h+=d
 raise AssertionError('Fixture did not halt within20steps')

def main():
 receipt=[]
 for name,flip,reverse in [('shift',False,True),('retag',True,False)]:
  old=read(HERE/'fixtures'/(name+'.tm'));new={}
  for(q,b),(w,d,n)in old.items():
   if q==1:continue
   if n==1:n=2;w=w^int(flip);d=-d if reverse else d
   new[q,b]=w,d,n
  a,b=run(old),run(new);assert a[:3]==b[:3]==(6,2,())
  assert a[3]==2 and b[3]==4
  receipt.append({'fixture':name,'old_steps':a[3],'new_steps':b[3],'terminal_control':a[0],'head':a[1],'complete_tape':list(a[2]),'exact_agreement':True})
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
