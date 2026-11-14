from local_scanner_screen import *
import time

def evaluated(z,limit):
 if bad(z):return None
 h,l,m,mi,first=attrs(z)
 if m>6 or mi>5:return None
 r,s=patched(z);lo=len(s)-len(c.max_matching(c.opportunities_fast(r,s)))
 if lo>limit:return None
 eff=len(s)-len(bestcompatible_all(r,s))
 return eff if eff<=limit else None

if __name__=='__main__':
 import sys
 t=c.read_grammar(sys.argv[1]);base=sb(t);seen={t};inter=[];start=time.time()
 for path,x in occurrences(t):
  for y in rotations(x):
   z=setpath(t,path,y)
   if z in seen:continue
   seen.add(z);bc=sb(z)
   if bc>=base:continue
   eff=evaluated(z,64)
   if eff is not None:inter.append((bc,eff,z))
 inter=sorted(inter,key=lambda x:(x[0]+3*(x[1]-62),x[0]))[:16]
 print('INTERMEDIATE',[(b,e)for b,e,t in inter],flush=True)
 best=base
 for b,e,t in inter:
  for x in nodes(t):
   for y in rotations(x):
    z=repl(t,x,y)
    if z in seen:continue
    seen.add(z);bc=sb(z)
    if bc>=best:continue
    eff=evaluated(z,62)
    if eff is not None:
     best=bc;name='scanner_two_'+str(bc);Path(name+'.grammar.json').write_text(json.dumps(encode(z),indent=2));print('BEST',best,eff,'seen',len(seen),'seconds',time.time()-start,flush=True)
 print('END',best,'seen',len(seen),'seconds',time.time()-start,flush=True)
