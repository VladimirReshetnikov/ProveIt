#!/usr/bin/env python3
"""Uniform and mixed decoder folds of the exact Context246 table.

All literal rows supporting current register induction contracts, including
incoming references, remain identical. Each candidate is tested on every
baseline-affected symbolic case and every survivor is rechecked on all8391.
A rejected affine computation is a bounded-checker result, not an impossibility
proof. No input artifact is modified. This is adapted in structure from the
attributed ProveIt permutation252 fold searches, using Context246's own oracle.
"""
from pathlib import Path
from collections import defaultdict,Counter
import argparse,json,sys,importlib.util,hashlib,time,os
ROOT=Path(__file__).resolve().parent
BASE=Path(os.environ.get('ZFC246_BASE',ROOT.parents[1]/'baseline/context246'))
TABLE=Path(os.environ.get('ZFC246_TABLE',BASE/'machine/zfc_prefix246_old.tm'))
sys.dont_write_bytecode=True

def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);sys.modules[name]=m;spec.loader.exec_module(m);return m
A=load('prefix246_search_affine',BASE/'sources/prior/prefix_affine.py')
L=load('prefix246_search_literal',BASE/'code/check_literal_instructions.py')
T0=L.read_table(TABLE)
T={(str(q),b):(w,'R'if d==1 else'L',str(t)) for (q,b),(w,d,t)in T0.items()}
STATES=sorted({q for q,b in T},key=int)
P=set()
def protect(x):
 if isinstance(x,dict):
  if {'state','read','row'}<=set(x):P.add((str(x['state']),x['read']))
  for v in x.values():protect(v)
 elif isinstance(x,list):
  for v in x:protect(v)
INDUCTIONS=json.loads((BASE/'results/macro-inductions.json').read_text())
assert [t['name']for t in INDUCTIONS['block_theorems']]==['seek73_block','carry95_block','return48_block','rollback112_block']
assert [t['name']for t in INDUCTIONS['macro_theorems']]==['positive_decrement','zero_decrement','increment']
assert [t['name']for t in INDUCTIONS['mark_theorems']]==[f'mark_{r}'for r in range(9)]
protect(INDUCTIONS)
assert len(P)==42
ORIGINAL=L.read_table(BASE/'machine/zfc_prefix246_old.tm')
assert all(T0[int(q),b]==ORIGINAL[int(q),b]for q,b in P), 'Changed induction-support row'
PROTECTED_TARGETS={T[k][2]for k in P}
DEAD=[q for q in STATES if q!='96' and q not in PROTECTED_TARGETS and all((q,b)not in P for b in (0,1))]

def successor(p,op,r,zero):
 if op=='CI' or op=='CD'and not zero:return L.add_one(p)
 if op=='CD':return L.add_one(L.remove_to(p,'0',1))
 if op=='CB':return L.add_one(L.remove_to(p,'0',r))
 if op=='CC':return L.remove_to(p,'1',r)
 return None
CASES=[]
for p,op,r in L.program_sites(BASE/'sources/Prog254.v'):
 for zero in ((True,False)if op=='CD'else(None,)):
  physical=L.PHYSICAL[r]if op in('CI','CD')else r
  guard=(physical,zero)if op=='CD'else None
  nxt=successor(p,op,r,zero)
  incgap=int(op=='CD'and not zero)
  effect=('inc',physical)if op=='CI'else('dec',physical)if op=='CD'and not zero else None
  right=[('b',int(c))for c in nxt or'']+[('r',0,1,40+incgap+int(nxt is None)-len(nxt or'')),('b',1),('box',('plain',effect))]
  CASES.append((p,op,r,zero,guard,A.canon([('b',1)],right)))
assert len(CASES)==8391
class Tracking(dict):
 def __init__(self,t):super().__init__(t);self.used=set()
 def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def check(t,i,fuel):
 p,op,r,z,guard,want=CASES[i]
 try:
  rules,steps=A.run(t,p,guard,want,halt=op=='CH',fuel=fuel)
  assert steps>0
  return True,sum(rules.values()),None
 except AssertionError as e:return False,0,'fuel'if str(e)=='symbolic fuel exhausted'else'unsupported'
 except KeyError:return False,0,'missing'

def bootstrap(t,limit):
 q,h,one='95',0,set()
 for tick in range(limit+1):
  if q=='96'and h-1 in one:
   # Complete root shape: marker, zero PC, header after>=40cells, primary
   # formula values0atlogicalT/W/H, at least one finite spare, blank exteriors.
   further=sorted(x for x in one if x>=h)
   if further and min(one)==h-1 and further[0]-h>=40:
    header=further[0];vals=[];j=header+1
    while j not in one and j+1 in one:
     k=j+1
     while k in one:k+=1
     vals.append(k-j-2);j=k
    if len(vals)>=10 and max(one)<j and all(vals[L.PHYSICAL[r]]==0 for r in (1,2,5)):
     return dict(outcome='complete_safe_root_candidate',steps=tick,head=h,header=header,values=vals[:9],spares=vals[9:],ones=sorted(one))
  if q=='254':return dict(outcome='halt',steps=tick)
  if tick==limit:return dict(outcome='fuel',steps=tick)
  w,d,q=t[q,int(h in one)]
  if w:one.add(h)
  else:one.discard(h)
  h+=1 if d=='R'else-1

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--family',choices=['uniform','mixed','both'],default='both');ap.add_argument('--fuel',type=int,default=1000);ap.add_argument('--seconds',type=float,default=600);ap.add_argument('--boot-limit',type=int,default=3000000);ap.add_argument('--output',type=Path);a=ap.parse_args()
 began=time.monotonic();usage=defaultdict(set);cost=[]
 for i in range(len(CASES)):
  t=Tracking(T);ok,n,e=check(t,i,a.fuel);assert ok,('baseline',i,e);cost.append(n)
  for k in t.used:usage[k].add(i)
 print('BASELINE8391 PASS;protected',len(P),'eligible',len(DEAD),flush=True)
 protected_proof_rows=sorted([list(p)for p in P],key=lambda p:(int(p[0]),p[1]))
 result=dict(table_sha256=hashlib.sha256(TABLE.read_bytes()).hexdigest(),family=a.family,fuel=a.fuel,baseline_cases=8391,protected_rows=protected_proof_rows,eligible_deletions=list(map(int,DEAD)),fixed_dispatch=96,start=95,finite_checker_rejection_not_impossibility=True,families={},survivors=[])
 lookup=defaultdict(list)
 for q in DEAD:lookup[q]=sorted(usage[q,0]|usage[q,1],key=lambda i:(cost[i],i))
 output=a.output or ROOT/f'{a.family}-fold-search246.json'
 def save():
  result['seconds']=time.monotonic()-began;output.write_text(json.dumps(result,indent=2)+'\n')
 for family in ([a.family]if a.family!='both'else['uniform','mixed']):
  g=dict(status='running',recipes=0,checks=0,full_rechecks=0,failures=Counter(),groups=[],survivors=[]);result['families'][family]=g
  stop=False
  for dead in DEAD:
   group=dict(deleted=int(dead),recipes=0,checks=0,first_failure_histogram=Counter());g['groups'].append(group)
   for keep in STATES:
    if keep==dead:continue
    for bit in ([None]if family=='uniform'else[0,1]):
     if family=='mixed':
      if keep=='96' or (keep,bit)in P:continue
      if keep in DEAD and int(keep)<int(dead):continue
      if T[dead,bit]==T[keep,bit]:continue
     if time.monotonic()-began>a.seconds:stop=True;break
     candidate={(q,b):(w,d,keep if t==dead else t)for(q,b),(w,d,t)in T.items()if q!=dead}
     if bit is not None:
      w,d,t=T[dead,bit];candidate[keep,bit]=(w,d,keep if t==dead else t)
     assert len(candidate)==490 and all(candidate[k]==T[k]for k in P)
     indices=lookup[dead]if bit is None else sorted(set(lookup[dead])|usage[keep,bit],key=lambda i:(cost[i],i))
     fail=None;error=None
     for i in indices:
      ok,n,error=check(candidate,i,a.fuel);g['checks']+=1;group['checks']+=1
      if not ok:fail=i;break
     if fail is None:
      for i in range(len(CASES)):
       ok,n,error=check(candidate,i,a.fuel);g['full_rechecks']+=1
       if not ok:fail=i;break
     g['recipes']+=1;group['recipes']+=1
     if fail is None:
      label=f'{family}_{dead}_{keep}_{bit}';path=ROOT/(label+'.tm')
      path.write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(candidate.items(),key=lambda x:(int(x[0][0]),x[0][1]))))
      boot=bootstrap(candidate,a.boot_limit)
      item=dict(deleted=int(dead),retained=int(keep),copied_read=bit,table=str(path),boot=boot)
      result['survivors'].append(item);g['survivors'].append(item);print('SURVIVOR',label,boot,flush=True)
     else:g['failures'][error]+=1;group['first_failure_histogram'][str(fail)]+=1
    if stop:break
   save()
   if int(dead)%20==0:print(family,'dead',dead,'recipes',g['recipes'],'seconds',round(time.monotonic()-began,2),flush=True)
   if stop:break
  g['status']='time_bound_partial'if stop else'completed';save();print('FAMILY',family,g['status'],'recipes',g['recipes'],'checks',g['checks'],'survivors',len(g['survivors']),flush=True)
  if stop:break
 result['status']='completed'if all(g['status']=='completed'for g in result['families'].values())else'partial';save()
 print('DONE',result['status'],'seconds',result['seconds'],flush=True)
if __name__=='__main__':main()
