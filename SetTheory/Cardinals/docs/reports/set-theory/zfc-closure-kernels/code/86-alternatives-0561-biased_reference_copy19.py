#!/usr/bin/env python3
"""Two forced-symbol identifications in the biased copier; 19 working states."""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import json,hashlib,itertools,random
import biased_reference_copy as B
OUT=Path(__file__).resolve().parent

def compile_copy(*, variable_anchor=False):
 table,start,ret,ids=B.compile_copy()
 if variable_anchor:
  a=ids['after_anchor'];table[a,1]=(1,'R',a)
 fold={ids['erase_first']:ids['return_left'],ids['erase_second']:ids['add_loop']}
 def q(x):return fold.get(x,x)
 # Removed states are entered only reading1; retained partner is entered only
 # reading0 under the universal valid-frame invariant.
 merged={(s,b):(w,d,q(t))for(s,b),(w,d,t)in table.items()if s not in fold}
 for dead,keep in fold.items():
  w,d,t=table[dead,1];merged[keep,1]=(w,d,q(t))
 order=sorted({s for s,b in merged});ren={s:i for i,s in enumerate(order)}|{ret:len(order)}
 result={(ren[s],b):(w,d,ren[t])for(s,b),(w,d,t)in merged.items()}
 return result,ren[start],ren[ret],{name:ren[q(i)]for name,i in ids.items()}

def main():
 T,s,ret,ids=compile_copy();assert ret==19;tests=0;maxsteps=0
 for a,b,c in itertools.product(range(5),repeat=3):
  for i in range(3):
   vals=[a,b,c];vals[i]+=2
   for extra in (2,3,8):maxsteps=max(maxsteps,B.check(T,s,ret,vals,i,vals[i]-2+extra));tests+=1
 rng=random.Random(1924618)
 for k in range(1000):
  vals=[rng.randrange(35)for _ in range(rng.randrange(1,16))];i=rng.randrange(len(vals));vals[i]+=2;gap=vals[i]+rng.randrange(0,30);c=rng.randrange(-30,31)
  _,_,end=B.frame(vals,i,gap,c);ext=[c-j for j in range(1,10)if rng.randrange(2)]+[end+j for j in range(10)if rng.randrange(2)]
  maxsteps=max(maxsteps,B.check(T,s,ret,vals,i,gap,c,ext));tests+=1
 text=f'#! start {s}\n'+''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(T.items()))
 (OUT/'biased_reference_copy_19.tm').write_text(text)
 result={'status':'PASS','working_states':ret,'operational_states':18,'rows':len(T),'states':ids,'tests':tests,'max_steps':maxsteps,'sha256':hashlib.sha256(text.encode()).hexdigest(),'scope':'Prepared-frame biased-reference copier; two forced-read state identifications justified by macro invariant.'}
 (OUT/'biased19_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
