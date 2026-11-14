from pathlib import Path
import sys,time,math,random,json,functools
root=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(root/'verification'),str(root/'math_reduction/grammar')]
import optimize_parameters as O
from rotate_search import tree,nodes,paths,replace,replace_one,expand
SIZES=[17,19,16,16,16,19]

def expression(word):
    t='old';stack=[]
    for c in word:
        if c in 'HAD':stack.append(t);t=c
        elif c=='P':stack.append(t);t=0
        elif c=='i':
            if isinstance(t,int):t+=1
            else:
                tag,a,b=t;t=(tag+1,a,b)
        elif c=='C':t=(0,stack.pop(),t)
        else:raise ValueError(c)
    assert stack==['old'],stack
    return t

def code(t):
    if isinstance(t,str):return [t]
    if isinstance(t,int):return ['P']+['i']*t
    tag,a,b=t;return code(a)+code(b)+['C']+['i']*tag

def antecedent_change(t,order,rng):
    j=rng.choice([j for j,head in enumerate(order)if head in(2,3,5)])
    lo=18+sum(SIZES[i]for i in order[:j]);hi=lo+SIZES[order[j]]
    word=expand(t);old=expression(word[lo:hi]);tag,a,right=old;tag2,b,c=right
    assert tag==tag2==0
    new=code((0,b,(0,a,c)));assert len(new)==hi-lo
    it=iter(word[:lo]+new+word[hi:])
    def go(q):
        if isinstance(q,str):return next(it)
        return go(q[0]),go(q[1])
    return go(t)

def main():
 budget=int(sys.argv[1])if len(sys.argv)>1 else 300000
 rng=random.Random(int(sys.argv[2])if len(sys.argv)>2 else 3141592)
 base=tree('x67');initial=tuple(range(6));best=196;bestt=(base,initial)
 t,order=bestt;score=best;start=time.monotonic();ties=[bestt]
 print('BASE',O.evaluate(base),flush=True);seen={base}
 for it in range(budget):
  if it%5000==0:t,order=rng.choice([bestt]+ties[-30:]);score=O.evaluate(t)[0]
  neworder=order;u=rng.random()
  if u<.015:cand,neworder=O.headswap(t,order,rng)
  elif u<.07:cand=antecedent_change(t,order,rng)
  elif u<.15:cand=O.parameter_change(t,order,rng)
  else:
   cand=t
   for _ in range(2 if rng.random()<.15 else 1):
    p,q=rng.choice(paths(cand));a,b=q
    if rng.randrange(2):
     if not isinstance(a,tuple):continue
     u,v=a;alt=(u,(v,b))
    else:
     if not isinstance(b,tuple):continue
     u,v=b;alt=((a,u),v)
    cand=replace(cand,q,alt)if rng.random()<.75 else replace_one(cand,p,alt)
  if cand in seen:continue
  seen.add(cand)
  if len(nodes(cand))>82:continue
  s,n,c,ds=O.evaluate(cand)
  temp=.9*(1-(it%5000)/5000)+.08
  if s<1000 and(s<=score or rng.random()<math.exp((score-s)/temp)):t=cand;order=neworder;score=s
  if s<=best:
   if s<best:best=s;bestt=(cand,neworder);ties=[];print('BEST',best,n,c,neworder,'iteration',it,'seconds',round(time.monotonic()-start,1),flush=True)
   ties.append((cand,neworder))
   if len(ties)>500:ties.pop(rng.randrange(400))
   if s<196:
    path=Path(__file__).with_name(f'antecedent_safe_{s}_{it}.json');O.output(cand,neworder,path)
    print('TARGET',path.name,ds,flush=True)
    if s<=194:break
  if it%10000==0:print('progress',it,'best',best,'current',score,'order',order,'seconds',round(time.monotonic()-start,1),flush=True)
 print('DONE','best',best,'visited',len(seen),'seconds',round(time.monotonic()-start,1),flush=True)
if __name__=='__main__':main()
