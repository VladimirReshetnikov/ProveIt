#!/usr/bin/env python3
"""Copy reference r from source field 1^(r+3) using a movable00 marker.

Prepared-frame component. The erased first1 is restored. Destination becomes
1^(r+1), preserving all other cells. Gap >= r+2; 21 working states.
"""
if not __debug__:raise RuntimeError('Assertions required')
from pathlib import Path
import json,itertools,random,hashlib
import marked_unary_copy as M
OUT=Path(__file__).resolve().parent

def compile_copy():
 old,_,ret,ids=M.compile_copy();inv={i:q for q,i in ids.items()}
 names_to_drop={'init','init_one','init_two','mark_first','finish_one_ones','finish_one_zero','finish_one_gap','two_ones','two_zero','two_gap','add_finish','add_two'}
 rows={(inv[q],b):(w,d,'RETURN'if t==ret else inv[t])for(q,b),(w,d,t)in old.items()if inv[q]not in names_to_drop}
 rows['init_bias',0]=(1,'R','erase_first');rows['init_bias',1]=(1,'R','erase_first')
 rows['erase_first',1]=(0,'R','erase_second');rows['erase_second',1]=(0,'R','next_source')
 names=['init_bias','erase_first','erase_second']+[q for q in ids if q not in names_to_drop]
 ni={q:i for i,q in enumerate(names)};nr=len(names)
 for q in names:
  for b in (0,1):
   if(q,b)not in rows:rows[q,b]=(b,'R','reject')
 table={(ni[q],b):(w,d,nr if t=='RETURN'else ni[t])for(q,b),(w,d,t)in rows.items()}
 return table,ni['init_bias'],nr,ni

def frame(vals,i,gap,c=0):
 r=vals[i]-2;assert r>=0 and gap>=r+2
 # M.frame's original larger capacity assertion is not needed for biased copy.
 tape={c};anchor=c+gap+1;tape.add(anchor);p=anchor+2;starts=[]
 for v in vals:
  assert v>=0;starts.append(p);tape.update(range(p,p+v+1));p+=v+2
 tape.remove(starts[i]);return tape,starts[i],p

def check(T,s,ret,vals,i,gap,c=0,ext=()):
 initial,p,end=frame(vals,i,gap,c);initial|=set(ext);r=vals[i]-2
 expected=initial|set(range(c,c+r+1))|{p}
 actual,h,steps,window=M.run(T,s,ret,initial,p)
 assert actual==expected,('tape',vals,i,gap,actual^expected)
 assert h==c+r and window[0]>=c and window[1]<=p+vals[i]+1
 return steps

def main():
 T,s,ret,ids=compile_copy();tests=0;maxsteps=0
 for a,b,c in itertools.product(range(5),repeat=3):
  for i in range(3):
   vals=[a,b,c];vals[i]+=2
   for extra in (2,3,8):
    maxsteps=max(maxsteps,check(T,s,ret,vals,i,vals[i]-2+extra));tests+=1
 rng=random.Random(2124618)
 for k in range(500):
  vals=[rng.randrange(35)for _ in range(rng.randrange(1,16))];i=rng.randrange(len(vals));vals[i]+=2;gap=vals[i]+rng.randrange(0,30);c=rng.randrange(-30,31)
  _,_,end=frame(vals,i,gap,c);ext=[c-j for j in range(1,10)if rng.randrange(2)]+[end+j for j in range(10)if rng.randrange(2)]
  maxsteps=max(maxsteps,check(T,s,ret,vals,i,gap,c,ext));tests+=1
 text=f'#! start {s}\n'+''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(T.items()))
 (OUT/f'biased_reference_copy_{ret}.tm').write_text(text)
 result={'status':'PASS','working_states':ret,'operational_states':ret-1,'rows':len(T),'separate_return':ret,'states':ids,'tests':tests,'max_steps':maxsteps,'sha256':hashlib.sha256(text.encode()).hexdigest(),'scope':'Reference field bias2; arbitrary whole-tape prepared frame. Not a full verifier.'}
 (OUT/'biased_results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
