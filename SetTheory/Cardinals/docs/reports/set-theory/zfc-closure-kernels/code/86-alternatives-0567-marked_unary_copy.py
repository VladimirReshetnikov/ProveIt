#!/usr/bin/env python3
"""Literal binary unary-field copier. Prepared-frame component only."""
if not __debug__: raise RuntimeError('Assertions required')
from pathlib import Path
import itertools,random,json,hashlib
OUT=Path(__file__).resolve().parent

def compile_copy():
 rows={}
 def p(q,b,w,d,t):
  assert (q,b)not in rows;rows[q,b]=(w,d,t)
 def equal(q,w,d,t):
  for b in (0,1):p(q,b,w if w is not None else b,d,t)
 p('init',0,1,'R','init_one')
 p('init_one',0,0,'L','done_ones');p('init_one',1,1,'R','init_two')
 p('init_two',0,0,'L','finish_one_ones');p('init_two',1,0,'L','mark_first')
 p('mark_first',1,0,'L','two_ones')
 for mode,cont in [('done','return_left'),('finish_one','add_finish'),('two','add_two'),('loop','add_loop')]:
  p(mode+'_ones',1,1,'L',mode+'_ones');p(mode+'_ones',0,0,'L',mode+'_zero')
  p(mode+'_zero',1,1,'L',mode+'_ones');p(mode+'_zero',0,0,'L',mode+'_gap')
  p(mode+'_gap',0,0,'L',mode+'_gap');p(mode+'_gap',1,1,'R',cont)
 p('add_finish',0,1,'R','return_left')
 p('return_left',0,0,'L','RETURN')
 p('add_two',0,1,'R','add_loop')
 p('add_loop',0,1,'R','gap_right')
 p('gap_right',0,0,'R','gap_right');p('gap_right',1,1,'R','after_anchor')
 p('after_anchor',0,0,'R','find_first')
 p('find_first',1,1,'R','find_ones');p('find_first',0,0,'R','next_source')
 p('find_ones',1,1,'R','find_ones');p('find_ones',0,0,'R','find_first')
 p('next_source',1,0,'L','back_one');p('next_source',0,0,'L','restore_right')
 p('back_one',0,0,'L','restore_old_left')
 p('restore_old_left',0,1,'L','loop_ones')
 p('restore_right',0,1,'L','restore_left')
 p('restore_left',0,1,'L','done_ones')
 names=list(dict.fromkeys(q for q,b in rows));names.append('reject');ids={q:i for i,q in enumerate(names)};ret=len(ids)
 for q in names:
  for b in (0,1):
   if (q,b)not in rows:rows[q,b]=(b,'R','reject')
 table={(ids[q],b):(w,d,ret if t=='RETURN' else ids[t])for(q,b),(w,d,t)in rows.items()}
 return table,ids['init'],ret,ids

def frame(vals,source,gap,c=0):
 assert vals and 0<=source<len(vals)and all(type(v)is int and v>=0 for v in vals)
 assert gap>=vals[source]+2
 tape={c};anchor=c+gap+1;tape.add(anchor);at=anchor+2;starts=[]
 for v in vals:
  starts.append(at);tape.update(range(at,at+v+1));at+=v+2
 tape.remove(starts[source]);return tape,starts[source],at,anchor

def run(t,start,ret,ones,h,limit=10000000):
 ones=set(ones);q=start;lo=hi=h;steps=0
 while q!=ret:
  if steps>=limit:raise RuntimeError(('fuel',q,h,steps))
  lo=min(lo,h);hi=max(hi,h);w,d,q=t[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R'else-1;steps+=1
 return ones,h,steps,(lo,hi)

def check(t,start,ret,vals,i,gap,c=0,ext=()):
 initial,source,end,anchor=frame(vals,i,gap,c);initial|=set(ext)
 expected=initial|set(range(c,c+vals[i]+1))|{source}
 actual,h,steps,window=run(t,start,ret,initial,source)
 assert actual==expected,('tape',vals,i,gap,sorted(actual^expected))
 assert h==c+vals[i],('head',h,c+vals[i])
 assert window[0]>=c and window[1]<=source+vals[i]+1,window
 return steps

def main():
 t,start,ret,ids=compile_copy();tests=0;maxsteps=0
 for length in range(1,5):
  for vals in itertools.product(range(4),repeat=length):
   for i in range(length):
    for extra in (2,3,8):
     gap=vals[i]+extra
     maxsteps=max(maxsteps,check(t,start,ret,vals,i,gap));tests+=1
 rng=random.Random(246102)
 for trial in range(2000):
  vals=[rng.randrange(100)for _ in range(rng.randrange(1,30))];i=rng.randrange(len(vals));gap=vals[i]+rng.randrange(2,80);c=rng.randrange(-50,51)
  _,s,e,a=frame(vals,i,gap,c);ext=[c-j for j in range(1,15)if rng.randrange(2)]+[e+j for j in range(15)if rng.randrange(2)]
  maxsteps=max(maxsteps,check(t,start,ret,vals,i,gap,c,ext));tests+=1
 text=f'#! start {start}\n'+''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(t.items()))
 (OUT/f'marked_unary_copy_{ret}.tm').write_text(text)
 result={'status':'PASS','working_states':ret,'separate_return':ret,'start':start,'rows':len(t),'states':ids,'tests':tests,'max_steps':maxsteps,'sha256':hashlib.sha256(text.encode()).hexdigest(),'scope':'Prepared-frame exact whole-tape copier; no complete verifier or blank initialization claim.'}
 (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
