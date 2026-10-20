from pathlib import Path
from collections import defaultdict
from functools import cache
import sys,json,itertools,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'machine-search'))
import prove_sym224_fold as p

def search(path,left=3,right=0):
 p.LEFT,p.RIGHT=left,right
 T=p.read(path);states=sorted({q for q,b in T});reached=p.fixpoint(T)
 windows=defaultdict(list);prev=defaultdict(set)
 for q,tape in reached:
  windows[q].append(tape);prev[q].add((tape>>(left-1))&1)
 tags={q:next(iter(bs))for q,bs in prev.items()if len(bs)==1}
 pure=[q for q in states if all(T[q,b][:2]==(b,1)for b in (0,1))]
 tagged=[q for q in pure if q in tags and q!=p.START]
 pairs=[]
 for bit in(0,1):
  for a in tagged:
   for b in tagged:
    if tags[a]==0 and tags[b]==1 and T[a,1-bit]==T[b,1-bit] and T[a,bit]!=T[b,bit]:pairs.append((bit,a,b))
 print('BASE',str(path),'window',left,right,'abstract',len(reached),'pairs',len(pairs),flush=True)
 @cache
 def choices(q,bit,hostwrite,rw,rd):
  target=T[q,bit][2];out=set()
  for u in states:
   good=True
   for original in windows[q]:
    if((original>>left)&1)!=bit:continue
    tape=(original&~(1<<left))|(hostwrite<<left)
    tape=(tape&~(1<<(left-1)))|(rw<<(left-1))
    state,head=u,left-1+rd
    for step in range(1,32):
     if not 0<=head<=left+right or state==p.HALT:break
     read=(tape>>head)&1;w,m,z=T[state,read]
     tape=(tape&~(1<<head))|(w<<head);state,head=z,head+m
     if(tape,head,state)==(original,left+1,target):break
    if(tape,head,state)!=(original,left+1,target):good=False;break
   if good:out.add(u)
  return out
 routeractions=list(itertools.product((0,1),(-1,1)))
 attempts=0;combinations=0
 for ix,(bit0,a,b)in enumerate(pairs):
  for bit1,c,d in pairs[ix+1:]:
   if len({a,b,c,d})!=4:continue
   for h0,h1 in itertools.product((0,1),repeat=2):
    for w0,d0 in routeractions:
     us=choices(a,bit0,h0,w0,d0)&choices(c,bit1,h1,w0,d0)
     if not us:continue
     for w1,d1 in routeractions:
      vs=choices(b,bit0,h0,w1,d1)&choices(d,bit1,h1,w1,d1)
      if not vs:continue
      for u,v in itertools.product(us,vs):
       attempts+=1;mp={b:a,d:c};phi=lambda q:mp.get(q,q)
       newq=max(states)+1
       if newq==p.HALT:newq+=1
       N={(q,bit):(w,m,phi(z))for(q,bit),(w,m,z)in T.items()if q not in mp}
       N[a,bit0]=(h0,-1,newq);N[c,bit1]=(h1,-1,newq)
       N[newq,0]=(w0,d0,phi(u));N[newq,1]=(w1,d1,phi(v))
       cert=[];good=True
       for q in(a,b,c,d):
        for original in windows[q]:
         tape=original;bit=(tape>>left)&1;w,m,z=T[q,bit]
         target=((tape&~(1<<left))|(w<<left),left+m,phi(z))
         head,state=left,phi(q);trace=[]
         for step in range(1,48):
          if not 0<=head<=left+right or state==p.HALT:break
          read=(tape>>head)&1;w,m,z=N[state,read];trace.append([state,head-left,read,w,m,z])
          tape=(tape&~(1<<head))|(w<<head);state,head=z,head+m
          if(tape,head,state)==target:cert.append(dict(state=q,window=original,trace=trace));break
         if(tape,head,state)!=target:good=False;break
        if not good:break
       if good:
        out=Path(__file__).parent/(path.parent.name+'-flex-winner');out.mkdir(exist_ok=True)
        (out/'candidate.legacy.tm').write_bytes(p.encode(N))
        result=dict(status='PASS_EXACT_TWO_FOLDS_ONE_NEW_ROUTER',parent=str(path),states=len(N)//2,removed=mp,new_router=newq,rows={str(k):v for k,v in N.items()if k[0]in(a,c,newq)},abstract_pairs=len(reached),left=left,right=right,certificates=cert,attempts=attempts)
        (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
        print('WINNER',out,'states',len(N)//2,'attempts',attempts,flush=True);return True
  print('PROGRESS',ix+1,len(pairs),'attempts',attempts,'choices',choices.cache_info().currsize,flush=True)
 print('DONE',str(path),'attempts',attempts,flush=True)
 return False

if __name__=='__main__':
 inputs=[Path('work/machine-search/sym224/candidate.legacy.tm'),Path('baseline/k224/K224_Construction_2026-10-20/portable/machine/results/candidate224.legacy.tm')]
 for path in inputs:
  if search(path):break
