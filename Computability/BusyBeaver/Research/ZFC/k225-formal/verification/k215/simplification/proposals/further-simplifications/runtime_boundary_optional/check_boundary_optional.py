#!/usr/bin/env python3
"""Owned optional Boundary-only fastpath. Does not modify frozen runtime_contexts.
A copy packaged beside runtime_contexts replays without network or external data.
"""
from pathlib import Path
import collections,itertools,json,sys
if not __debug__:raise SystemExit('Assertions must be enabled')
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'runtime_contexts'))
import symbolic_owned as a
from profile_home import M,home,tasks
from verify_home import concrete,tape_run

def boundary(s):
 q,onl,l,r=s
 if q!=2 or not onl or not r or r[0]!=a.bit(True):return None
 if any(x[0]not in('bit','run')or x[1]for x in l):return None
 return (84,False,(a.bit(True),),r[1:])

def freeze(x):return tuple(map(freeze,x))if type(x)is list else x

def exact_rejections():
 prior=json.loads((ROOT.parent/'runtime_contexts'/'home_independent_result.json').read_text())
 rows=[]
 for ex in prior['accelerated_symbolic_runner']['conservative_guard_rejections']:
  s=freeze(ex['state']);t=boundary(s);assert home(s)is None and t is not None
  br=freeze(ex['branch']);now=s;positive=False;steps=0
  while steps<100:
   nxt=a.sstep(M,br,now);assert nxt is not None
   now,m=nxt;positive|=m;steps+=1
   if now[0]==84 and not now[1]:break
  assert positive and a.matches(now,t)
  rows.append({'path':ex['path'],'kind':ex['kind'],'branch':ex['branch'],'input':s,'output':t,'old_symbolic_steps':steps,'new_dispatches':1,'saved_symbolic_dispatches':steps-1})
 assert len(rows)==2
 return rows

def finite_support():
 count=0
 for size in range(9):
  for rt in itertools.product((False,True),repeat=size):
   for k in [0,1,7,8,31]:
    s=(2,True,(a.run(False,0,k),),(a.bit(True),)+tuple(map(a.bit,rt)))
    out=boundary(s);assert out is not None
    q,h,ones=concrete(s,0);q2,h2,ones2=tape_run(q,h,ones,18)
    oq,oh,oones=concrete(out,0)
    assert(q2,h2,ones2)==(oq,oh+1,{i+1 for i in oones})
    assert ones2==ones
    count+=1
 symbolic=0
 for n in [0,1,2,17,100]:
  for coef in [0,1,3]:
   for c in [0,1,8,31]:
    s=(2,True,(a.run(False,coef,c),),(a.bit(True),a.bit(False),a.bit(True)))
    out=boundary(s);q,h,ones=concrete(s,n);oq,oh,oo=concrete(out,n)
    assert tape_run(q,h,ones,18)==(oq,oh+1,{i+1 for i in oo})
    symbolic+=1
 for s in [(3,True,(),(a.bit(True),)),(2,False,(),(a.bit(True),)),(2,True,(a.bit(True),),(a.bit(True),)),(2,True,(),(a.bit(False),)),(2,True,(),(a.run(True,1,0),))]:assert boundary(s)is None
 return {'complete_tape_cases':count,'symbolic_padding_cases':symbolic,'negative_guards_rejected':5,'physical_duration':18}

def accelerated():
 counts=collections.Counter();used=[]
 for p,(kind,reg)in a.sites():
  for br,tgt in tasks(p,kind,reg):
   s=a.start(p);moved=False
   for f in range(4000):
    if moved and(s[0]==230 if tgt is None else a.matches(s,tgt)):break
    hs=home(s)
    if hs is not None:s=hs;moved=True;counts['home_macros']+=1
    else:
     bs=boundary(s)
     if bs is not None:
      used.append({'path':''.join(str(int(b))for b in p),'kind':kind,'branch':br})
      s=bs;moved=True;counts['boundary_macros']+=1
     else:
      nxt=a.sstep(M,br,s);assert nxt is not None
      s,m=nxt;moved|=m;counts['ordinary_steps']+=1
   else:raise AssertionError(('fuel exhausted',p,kind,reg))
   counts['runs']+=1;counts['total_dispatches']+=f
 assert counts['runs']==6176 and counts['boundary_macros']==2
 return {'counts':dict(counts),'boundary_uses':used}
if __name__=='__main__':
 out={'status':'PASS_DATA_ONLY_NOT_KERNEL_PROOF','scope':'Optional addition using the same Boundary lemma; primary frozen artifacts unchanged.','exact_prior_rejections':exact_rejections(),'independent_complete_tape_checks':finite_support(),'accelerated_runner':accelerated()}
 old=2442801;now=out['accelerated_runner']['counts']['total_dispatches']
 out['comparison']={'old_dispatches':old,'primary_home_dispatches':926351,'optional_dispatches':now,'additional_saved':926351-now,'total_saved':old-now,'total_saved_fraction':(old-now)/old}
 (ROOT/'boundary_optional_result.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k!='exact_prior_rejections'},indent=2))
