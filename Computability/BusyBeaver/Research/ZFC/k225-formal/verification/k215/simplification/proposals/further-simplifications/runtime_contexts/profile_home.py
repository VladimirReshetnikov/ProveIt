#!/usr/bin/env python3
"""Independent profile: every proposed home macro is checked against old symbolic execution.
The structural row conditions give a mathematical universal-word contract; finite replay
is a regression audit, not its formal Lean proof.
"""
from pathlib import Path
import collections,hashlib,json,copy
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import symbolic_owned as a
ROOT=Path(__file__).resolve().parent
if not __debug__:raise SystemExit('Assertions must be enabled')
T=a.table_def(a.read('KTable215.lean'),'table215','\ndef tm215')
def M(q,b):return T[q][b] if q<len(T) else None
STATES=[2,3,5,9,15,23,34,50]
for i,q in enumerate(STATES):
 assert M(q,True)==(True,False,2)
 assert M(q,False)==(False,False,STATES[i+1] if i<7 else 75)
assert M(75,False)==(False,True,75) and M(75,True)==(True,True,84)

def home(s):
 q,onl,l,r=s
 if q!=2 or not onl:return None
 # Remove only trailing blank segments, the physical blank left exterior.
 i=len(l)
 while i and (l[i-1][0]=='bit' and not l[i-1][1] or l[i-1][0]=='run' and not l[i-1][1]):i-=1
 w=l[:i]
 if not w or w[-1]!=a.bit(True):return None
 # At n=0 the true runs are shortest. Removing true cells can only increase zero streaks.
 z=0
 for x in w:
  if x[0]=='bit':
   z=0 if x[1] else z+1
  elif x[0]=='run':
   _,b,coef,c=x
   if b:
    if c:z=0
   else:
    if coef:return None
    z+=c
  else:return None
  if z>=8:return None
 return (84,False,(a.bit(True),),tuple(reversed(w[:-1]))+r)

def tasks(p,k,r):
 if k=='inc':return [(None,a.target(a.inc(p),all(p),('plain','inc',a.PHYS[r])))]
 if k=='decnz':return [((a.PHYS[r],True),a.target(a.brk(p,1),all(a.strip(p,False,1)),a.PLAIN)),((a.PHYS[r],False),a.target(a.inc(p),all(p),('plain','dec',a.PHYS[r])))]
 if k=='brk':return [(None,a.target(a.brk(p,r),all(a.strip(p,False,r)),a.PLAIN))]
 if k=='cont':return [(None,a.target(a.cont(p,r),False,a.PLAIN))]
 assert k=='halt';return [(None,None)]

def run():
 counts=collections.Counter();blocked=collections.Counter();examples={};cert=[]
 for p,(kind,reg) in a.sites():
  for br,tgt in tasks(p,kind,reg):
   s=a.start(p);moved=False;old_steps=new_steps=0;cuts=[]
   while old_steps<4000:
    if moved and (s[0]==230 if tgt is None else a.matches(s,tgt)):break
    h=home(s)
    if h is not None:
     before=s;t=s;positive=False;j=0
     while j<4000:
      out=a.sstep(M,br,t);assert out is not None
      t,m=out;positive|=m;j+=1
      if t[0]==84 and not t[1]:break
     assert j<4000 and positive and a.matches(t,h),(p,kind,reg,before,t,h)
     counts['macros']+=1;counts['old_steps_in_home']+=j;counts['macro_steps_saved']+=j-1
     counts['home_'+kind]+=1;cuts.append([old_steps,j]);old_steps+=j
     examples.setdefault(kind,{'path':''.join(str(int(b))for b in p),'branch':br,'symbolic_steps':j,'input':before,'output':h})
     # Keep the original raw output so later replay is exactly the pre-existing program.
     s=t;moved=True
    else:
     if s[0]==2 and s[1]:blocked[kind]+=1
     out=a.sstep(M,br,s);assert out is not None
     s,m=out;moved|=m;old_steps+=1
    new_steps+=1
   else:raise AssertionError(('fuel exhausted',p,kind,reg))
   counts['runs']+=1;counts['old_total_steps']+=old_steps;counts['macro_runner_steps']+=new_steps
   cert.append({'path':''.join(str(int(b))for b in p),'edge':[kind,reg],'branch':br,'cuts':cuts,'old_steps':old_steps})
 result={'status':'PASS_DATA_ONLY_NOT_KERNEL_PROOF','table_row_conditions_checked':18,'counts':dict(counts),'rejected_candidates':dict(blocked),'examples':examples,'saved_fraction':counts['macro_steps_saved']/counts['old_total_steps']}
 (ROOT/'home_profile.json').write_text(json.dumps(result,indent=2)+'\n')
 (ROOT/'home_cuts.json').write_text(json.dumps(cert,separators=(',',':'))+'\n')
 print(json.dumps({k:v for k,v in result.items()if k!='examples'},indent=2))
if __name__=='__main__':run()
