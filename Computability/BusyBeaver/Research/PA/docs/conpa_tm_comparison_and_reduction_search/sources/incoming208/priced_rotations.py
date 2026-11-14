#!/usr/bin/env python3
"""Bounded AX layout search with actual compatible local-fold pricing."""
import compile_ax as c
import json,pathlib,random,time,math,sys
g=c.g;OUT=c.HERE
def main():
 base=g.get_macro_tree()[2]
 rng=random.Random(73931)
 cache={}
 def score(t):
  if t not in cache:cache[t]=c.price(t)
  return cache[t]
 n=0;best=base;bv,bs=score(base);cur=base;v=bv;begin=time.time()
 print('BASE',bv,len(g.nodes(base)),len(bs),flush=True)
 budget=int(sys.argv[1]) if len(sys.argv)>1 else 240
 while time.time()-begin<budget:
  n+=1
  if n%2500==0:cur=base if n%5000==0 else best;v=score(cur)[0]
  choices=list(g.nodes(cur));q=rng.choice(choices);l,r=q
  if isinstance(l,tuple) and (isinstance(r,str) or rng.random()<.5):a=(l[0],(l[1],r))
  elif isinstance(r,tuple):a=((l,r[0]),r[1])
  else:continue
  t=g.replace(cur,q,a)
  nc=len(g.nodes(t))
  if nc>73:continue
  tv,ts=score(t)
  temp=.03+.75*(1-(n%2500)/2500)**4
  if tv<v or tv==v or rng.random()<math.exp((v-tv)/temp):cur,v=t,tv
  if tv<bv:
   best,bv,bs=t,tv,ts
   print('BEST',bv,'nodes',nc,'folds',len(ts),'iteration',n,'seconds',time.time()-begin,flush=True)
   (OUT/f'priced_best_{bv}.json').write_text(json.dumps({'tree':t,'folds':ts,'states':bv},indent=2))
   if bv<196:break
  if n%1000==0:print('PROGRESS',n,'best',bv,'current',v,'cache',len(cache),'seconds',time.time()-begin,flush=True)
 print('DONE',n,'best',bv,'cache',len(cache),'seconds',time.time()-begin,flush=True)
 (OUT/'priced_search_receipt.json').write_text(json.dumps({'iterations':n,'best_count':bv,'layouts_priced':len(cache),'seconds':time.time()-begin,'method':'random global rotations; puretree compiler; compatible3stepold-predecessor-tagfolds'},indent=2))
if __name__=='__main__':main()
