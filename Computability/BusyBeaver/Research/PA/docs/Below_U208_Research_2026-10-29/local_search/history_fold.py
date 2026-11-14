#!/usr/bin/env python3
from pathlib import Path
import argparse,json,random,time
from history_search import read,histories,finite,exact

def main():
    a=argparse.ArgumentParser();a.add_argument('table');a.add_argument('--depth',type=int,default=5);a.add_argument('--limit',type=int,default=20);a.add_argument('--output',required=True);a=a.parse_args()
    t=read(a.table);ctxs,counts=histories(t,a.depth);rng=random.Random(293626)
    states=sorted({q for q,b in t});start=time.monotonic();results=[];scans=0;pairs=0
    for i,q in enumerate(states):
      for r in states[:i]:
        if 0 in(q,r):continue
        for bit in(0,1):
          if t[q,1-bit]!=t[r,1-bit]:continue
          if any(z in(q,r) for w,d,z in [t[q,b] for b in (0,1)]+[t[r,b] for b in (0,1)]):continue
          pairs+=1
          for h in states:
            if h==q:continue
            for w in(0,1):
              for d in(-1,1):
                scans+=1
                nt={(s,b):(v,e,r if z==q else z) for(s,b),(v,e,z)in t.items() if s!=q};nt[r,bit]=(w,d,h)
                if not all(finite(t,nt,s,r,c,b,rng,a.limit) for s in(q,r) for c in ctxs[s] for b in(bit,1-bit) for _ in range(2)):continue
                cert=[]
                for s in(q,r):
                  for c in ctxs[s]:
                    for b in(0,1):
                      ex=exact(t,nt,s,r,c,b,a.limit)
                      if ex is None:break
                      cert.append({'old_state':s,'context':c,'read':b,'branches':ex})
                    else:continue
                    break
                  else:continue
                  break
                else:
                  results.append({'remove':q,'representative':r,'row':[r,bit,w,d,h],'cases':cert});print('FOLD',q,r,[r,bit,w,d,h],flush=True)
    result={'input':a.table,'depth':a.depth,'limit':a.limit,'pairs':pairs,'scans':scans,'seconds':time.monotonic()-start,'folds':results}
    Path(a.output).write_text(json.dumps(result,indent=2)+'\n');print('DONE',len(results),pairs,scans,result['seconds'])
if __name__=='__main__':main()
