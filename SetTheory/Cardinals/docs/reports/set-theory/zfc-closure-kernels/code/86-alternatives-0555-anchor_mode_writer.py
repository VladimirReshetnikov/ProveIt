#!/usr/bin/env python3
"""11-state four-entry fixed-width anchor mode writer; prepared-frame only."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import json,itertools,hashlib,random
OUT=Path(__file__).parent

def compile_writer():
 names=[f'unseen{i}'for i in range(5)]+[f'seen{i}'for i in range(3)]+['old_zero','final_zero','reject'];ids={q:i for i,q in enumerate(names)};ret=len(names);rows={}
 def p(q,b,w,d,t):rows[ids[q],b]=(w,d,ret if t=='RETURN'else ids[t])
 for j in range(1,5):
  p(f'unseen{j}',1,1,'R',f'unseen{j-1}')
  p(f'unseen{j}',0,1,'R',f'seen{j-1}'if j<=3 else'reject')
 for j in range(1,3):
  p(f'seen{j}',1,1,'R',f'seen{j-1}')
 p('unseen0',0,0,'R','final_zero');p('unseen0',1,0,'R','old_zero')
 p('seen0',1,0,'R','final_zero')
 p('old_zero',1,1,'R','old_zero');p('old_zero',0,1,'R','final_zero')
 p('final_zero',1,1,'R','final_zero');p('final_zero',0,0,'R','RETURN')
 for q in names:
  for b in (0,1):
   if(ids[q],b)not in rows:p(q,b,b,'R','reject')
 return rows,{k:ids[f'unseen{k}']for k in range(1,5)},ret,ids

def header(k):return [1]*k+[0]+[1]*(5-k)+[0]
def execute(T,entry,ret,ones,h):
 ones=set(ones);q=entry;n=0;visited=[]
 while q!=ret:
  assert n<30;(visited.append((q,h,int(h in ones))))
  w,d,q=T[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R'else-1;n+=1
 return ones,h,n,visited

def main():
 T,E,ret,ids=compile_writer();count=0;vis=set()
 for old,new,offset,left,right in itertools.product(range(1,5),range(1,5),(-10,0,11),range(8),range(8)):
  initial={offset+i for i,b in enumerate(header(old))if b}
  initial|={offset-1-i for i in range(3)if(left>>i)&1}|{offset+7+i for i in range(3)if(right>>i)&1}
  wanted=(initial-set(range(offset,offset+7)))|{offset+i for i,b in enumerate(header(new))if b}
  out,h,n,trace=execute(T,E[new],ret,initial,offset)
  assert out==wanted and h==offset+7 and n==7 and all(offset<=p<offset+7 for q,p,b in trace)
  count+=1;vis.update(q for q,p,b in trace)
 text='# entries='+json.dumps(E,sort_keys=True)+'\n'+''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(T.items()))
 (OUT/'anchor_mode_writer_11.tm').write_text(text)
 result={'status':'PASS','states':ret,'operational_states':ret-1,'rows':len(T),'entries':E,'separate_return':ret,'tests':count,'steps_each':7,'all_operational_exercised':len(vis)==ret-1,'names':ids,'sha256':hashlib.sha256(text.encode()).hexdigest(),'scope':'Mode already in control entry; reading desiredmode and reachingheader requirechargedcaller.'}
 (OUT/'anchor_mode_writer_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
