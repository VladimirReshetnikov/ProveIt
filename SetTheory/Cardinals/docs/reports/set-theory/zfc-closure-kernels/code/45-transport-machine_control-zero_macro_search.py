#!/usr/bin/env python3
"""Search shared identity macros certified by zero register guards.

A closed node whose first edge is DECNZ(r) returns normally without
changing any register when r=0. At the two globally forced-zero loop
entries, replace the whole loop with any existing such identity macro.
This searches program grammar sharing rather than deleting instructions.
"""
import json
from pathlib import Path
from collections import Counter
from functools import lru_cache
from compile_global import BASE,HERE,parse,tree,intern,bounds,compile_t
from verify_register_certificate import check

def main():
 _,raw,_=parse(BASE/'Prog254.v');t=tree(raw);nodes,root=intern(t)
 @lru_cache(None)
 def expand(e):
  return ('N',*(expand(x) for x in nodes[e[1]])) if e[0]=='N' else e
 certificates=[check(BASE/'Prog254.v',HERE/name) for name in ('register_abstract_np0.json','register_abstract_k3.json')]
 zeroes=[{r for r in range(9) if all(c['forced_entry_masks'][str(site)][r]==1 for c in certificates)} for site in (6316,6434)]
 assert zeroes==[{3,5,6,7},{1,3,5,6,7}]
 prefixes=['11101001011000110','11111100']
 options=[]
 for z in zeroes:
  options.append([(-1,('B',0))]+[(n,expand(('N',n))) for n,(a,b) in nodes.items() if a[0]=='D' and a[1] in z and bounds(expand(('N',n)))==(0,0)])
 def rewrite(repl):
  def go(e,p):
   if p in repl:return repl[p]
   if e[0]!='N':return e
   a,b=go(e[1],p+'0'),go(e[2],p+'1')
   if a==('B',0) and bounds(b)==(0,0):return b
   if b==('B',0) and bounds(a)==(0,0):return a
   return ('N',a,b)
  return go(t,'')
 hist=Counter();best=999;winners=[];best_t=None;trials=[]
 for n,a in options[0]:
  for m,b in options[1]:
   u=rewrite(dict(zip(prefixes,(a,b))));count=len(intern(u)[0]);hist[count]+=1;trials.append([n,m,count])
   if count<best:best=count;winners=[(n,m)];best_t=u;print('best',best,n,m,flush=True)
   elif count==best:winners.append((n,m))
 r=compile_t(best_t,'global_zero_macro_best')
 out={'candidate_counts':list(map(len,options)),'trials':trials,'histogram':dict(hist),'best_nodes':best,'winners':winners,'compiled':r,
      'source_prefixes':prefixes,'zero_registers':list(map(sorted,zeroes)),
      'scope':'Finite grammar search using two checked register-zero guards; not a new binary correctness proof.'}
 (HERE/'zero_macro_search.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='trials'},indent=2))
if __name__=='__main__':main()
