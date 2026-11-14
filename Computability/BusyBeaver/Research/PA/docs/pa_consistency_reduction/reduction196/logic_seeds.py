from optimize_logic import *
import search_grammar as SG

def special_path(t,token,p=()):
 if isinstance(t,str):return p if t==token else None
 z=special_path(t[0],token,p+(0,))
 return z if z is not None else special_path(t[1],token,p+(1,))
def at(t,p):
 for b in p:t=t[b]
 return t

def join(a,b):return b if a is None else a if b is None else (a,b)
def extractlast(t):
 if isinstance(t,str):return None,t
 pre,last=extractlast(t[1]);return join(t[0],pre),last

def extractfirst(t):
 if isinstance(t,str):return t,None
 first,post=extractfirst(t[0]);return first,join(post,t[1])

def repair(t):
 for _ in range(10):
  changed=False
  for token,tag in [('R',0),('S',0),('G',1)]:
   p=special_path(t,token)
   if p[-1]==tag:continue
   indices=[i for i,b in enumerate(p)if b==tag]
   if not indices:return None
   k=indices[-1];pp=p[:k];a,b=at(t,pp)
   if tag==0:
    pre,last=extractlast(a);assert last==token and pre is not None
    new=pre,(last,b)
   else:
    first,post=extractfirst(b);assert first==token and post is not None
    new=(a,first),post
   t=replace_one(t,pp,new);changed=True
  if not changed:return t
 return None

def seeds():
 base=tree('x67');order=tuple(range(6));out={}
 for fm in[False,True]:
  for fe in[False,True]:
   for gx in[False,True]:
    d=fm,fe,gx;t=change(base,order,fm,fe,gx);best=O.evaluate(t)[0];bestt=t
    SG.WORD=expand(t)
    for seed in range(100):
     rules,rt=SG.repaire(seed,0 if seed%2 else .5)
     def dec(q):return tuple(map(dec,rules[q]))if q in rules else q
     cand=repair(dec(rt))
     if cand is None:continue
     s=O.evaluate(cand)[0]
     if s<best:best=s;bestt=cand
    out[d]=(best,bestt)
    print('SEED',d,best,len(nodes(bestt)),flush=True)
 return out

if __name__=='__main__':
 for d,(s,t)in seeds().items():
  p=Path(__file__).with_name('logic_seed_'+''.join(str(int(x))for x in d)+'.json')
  O.output(t,tuple(range(6)),p)
