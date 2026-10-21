#!/usr/bin/env python3
"""Independent finite-support verification of the universal scanner contract.
This tests words exhaustively and symbolically accelerated entire site runs.
It does not substitute for proving the stated induction in Lean.
"""
from pathlib import Path
import collections,itertools,json,random
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import symbolic_owned as a
from profile_home import home,tasks,M
ROOT=Path(__file__).resolve().parent
if not __debug__:raise SystemExit('Assertions must be enabled')

def concrete(s,n):
 def flatten(xs):
  out=[]
  for x in xs:
   if x[0]=='bit':out.append(x[1])
   elif x[0]=='run':out.extend([x[1]]*(x[2]*n+x[3]))
   else:raise ValueError('The scanner test uses opaque ordinary right words, not a box oracle')
  return out
 q,onl,l,r=s;l=flatten(l);r=flatten(r)
 # Absolute origin is the right-list boundary; zl has head one cell to its left.
 ones={-i-1 for i,b in enumerate(l)if b}|{i for i,b in enumerate(r)if b}
 return q,-1 if onl else 0,ones

def tape_run(q,h,ones,steps):
 ones=set(ones)
 for _ in range(steps):
  row=M(q,h in ones);assert row is not None
  w,right,q=row
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if right else -1
 return q,h,ones

def finite_checks():
 cases=0;rights=[(),(True,),(False,True),(True,False,True,False)]
 for size in range(13):
  for u in itertools.product((False,True),repeat=size):
   w=u+(True,)
   if '00000000'in ''.join(str(int(b))for b in w):continue
   # Left list read leftwards. Final true is the leftmost marker.
   for rt in rights:
    s=(2,True,tuple(map(a.bit,w))+(a.run(False,0,3),),tuple(map(a.bit,rt)))
    hs=home(s);assert hs is not None
    q,h,ones=concrete(s,0);q2,h2,ones2=tape_run(q,h,ones,len(w)+18)
    assert(q2,h2,ones2)==(84,-len(w)+1,ones)
    # Relative output translates its boundary to the cell right of the leftmost marker.
    eq,eh,eones=concrete(hs,0);shift=-len(w)+1
    assert q2==eq and h2==eh+shift and ones2=={i+shift for i in eones}
    cases+=1
 rng=random.Random(215)
 symbolic=0
 for _ in range(300):
  u=tuple(a.bit(bool(rng.randrange(2)))for _ in range(rng.randrange(15)))
  # The n-coefficient true run is guaranteed to reset for c>=1.
  w=u+(a.run(True,rng.randrange(1,4),rng.randrange(1,4)),a.bit(False),a.bit(True))
  pad=(a.run(False,rng.randrange(4),rng.randrange(10)),)
  rt=tuple(a.bit(bool(rng.randrange(2)))for _ in range(12))
  s=(2,True,w+pad,rt);hs=home(s)
  if hs is None:continue
  for n in [0,1,2,7,31]:
   q,h,ones=concrete(s,n)
   length=sum(1 if x[0]=='bit' else x[2]*n+x[3] for x in w)
   q2,h2,ones2=tape_run(q,h,ones,length+18);eq,eh,eps=concrete(hs,n)
   assert(q2,h2,ones2)==(eq,eh-length+1,{i-length+1 for i in eps})
   symbolic+=1
 negatives={
  'eight_zeros_before_marker':(2,True,tuple(map(a.bit,[False]*8+[True])),()),
  'missing_marker':(2,True,(a.run(False,0,20),),()),
  'wrong_entry_state':(3,True,(a.bit(True),),()),
  'unbounded_false_run_inside_word':(2,True,(a.run(False,1,0),a.bit(True)),()),
  'vanishing_true_run_joins_eight_zeros':(2,True,(a.run(False,0,4),a.run(True,1,0),a.run(False,0,4),a.bit(True)),()),
 }
 for label,s in negatives.items():assert home(s)is None,label
 return {'exhaustive_whole_tape_cases':cases,'symbolic_instantiation_cases':symbolic,'negative_guards':{k:'rejected'for k in negatives}}

def accelerated():
 c=collections.Counter();rejected=[]
 for p,(kind,reg)in a.sites():
  for br,tgt in tasks(p,kind,reg):
   s=a.start(p);moved=False
   for f in range(4000):
    if moved and(s[0]==230 if tgt is None else a.matches(s,tgt)):break
    hs=home(s)
    if hs is not None:s=hs;moved=True;c['macros']+=1
    else:
     if s[0]==2 and s[1]:rejected.append({'path':''.join(str(int(b))for b in p),'kind':kind,'branch':br,'state':s})
     out=a.sstep(M,br,s);assert out is not None,(p,kind,reg,s)
     s,m=out;moved|=m;c['ordinary_steps']+=1
   else:raise AssertionError(('fuel exhausted',p,kind,reg))
   c['runs']+=1;c['total_steps']+=f
 return {'counts':dict(c),'conservative_guard_rejections':rejected}
if __name__=='__main__':
 out={'status':'PASS_DATA_ONLY_NOT_KERNEL_PROOF','finite_support_checker':finite_checks(),'accelerated_symbolic_runner':accelerated()}
 (ROOT/'home_independent_result.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k!='accelerated_symbolic_runner'},indent=2));print(out['accelerated_symbolic_runner']['counts'])
