#!/usr/bin/env python3
"""State deletion using ranked control-bisimulation continuation contracts.

This is a bounded mathematical diagnostic, not a kernel proof and not a
minimum-state claim. Its four unchanged register-box contracts retain their
prior scope. The full program and literal complete252 table are preserved.
"""
from pathlib import Path
from collections import defaultdict,Counter
from types import SimpleNamespace
import argparse,hashlib,importlib.util,json,sys,time
import candidate252_independent_audit as audit
from control_bisim import build

BASE=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.modules['cost_search']=SimpleNamespace()
spec=importlib.util.spec_from_file_location('strict',BASE/'27-variant-experiments-machine_search-grammar_search-strict_affine.py')
strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)

class Track(dict):
 def __init__(self,rows):super().__init__(rows);self.used=set()
 def __getitem__(self,key):self.used.add(key);return super().__getitem__(key)

class Patch:
 def __init__(self,base,dead,redirect=None,row=None,action=None):self.base=base;self.dead=dead;self.redirect=redirect;self.row=row;self.action=action
 def __getitem__(self,key):
  if key[0]==self.dead:raise KeyError(key)
  if key==self.row:return self.action
  w,d,t=self.base[key]
  return w,d,self.redirect if t==self.dead else t

class Framework:
 def __init__(self):
  raw=(BASE/'candidate-permutation252_zfc_permutation252_old.tm').read_bytes()
  assert hashlib.sha256(raw).hexdigest()==audit.EXPECTED_SHA
  numeric=audit.read_table(raw)
  self.table={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in numeric.items()}
  self.states=sorted({q for q,b in self.table},key=int)
  self.protected={(str(q),b)for q,b in audit.BOX_PAIRS}
  self.sites,self.cases,self.targets,self.first,self.bysite,self.closure,self.rank,self.classes,self.counts=build()
  self.trie={}
  for i,(p,op,r) in enumerate(self.sites):
   d=self.trie
   for b in p:d=d.setdefault(b,{})
   d['leaf']=i
  self.target=[]
  for i,(site,p,op,r,zero)in enumerate(self.cases):
   physical=audit.NEWPHYS[r]if op in('CI','CD')else r
   effect=('inc',physical)if op=='CI'else('dec',physical)if op=='CD'and not zero else None
   self.target.append(Target(self,i,effect))
  self.numeric=numeric
 def decode(self,pc):
  d=self.trie;k=0
  while 'leaf'not in d:
   d=d[pc[k]if k<len(pc)else'0'];k+=1
  if '1'in pc[k:]:return None
  return d['leaf']
 def check(self,current,i,fuel):
  site,p,op,r,zero=self.cases[i]
  branch=(audit.NEWPHYS[r],zero)if op=='CD'else None
  try:
   target=self.target[i];target.accepted=None
   rules,literal=strict.run(current,p,branch,target,halt=op=='CH',fuel=fuel)
   assert literal>0
   return True,sum(rules.values()),target.accepted
  except AssertionError as exc:
   reason=str(exc)
   if reason=='symbolic fuel exhausted':reason='fuel'
   elif 'unknown left-run length'in reason:reason='unknown_left_run'
   elif 'unknown right-run length'in reason:reason='unknown_right_run'
   elif 'no justified box operation'in reason:reason='unsupported_box'
   else:reason='unsupported_symbolic_rule'
   return False,0,reason
  except KeyError:return False,0,'missing_transition'
 def baseline(self,fuel):
  self.usage=defaultdict(list);self.row_usage=defaultdict(list)
  for i in range(len(self.cases)):
   traced=Track(self.table);ok,steps,out=self.check(traced,i,fuel);assert ok,('baseline',i,out)
   for key in traced.used:self.row_usage[key].append((steps,i))
   for q in {q for q,b in traced.used}:self.usage[q].append((steps,i))
  for group in list(self.usage.values())+list(self.row_usage.values()):group.sort()
  q,h,ones,_,_=audit.run_prefix(self.numeric,82552)
  spares=[0]*65;spares[8]=1
  assert(q,h,ones)==(96,2,audit.paint('',40,[0]*9,spares,2))
  return {'cases':len(self.cases),'blank_boot':82552,'old_table_sha256':audit.EXPECTED_SHA}

class Target:
 def __init__(self,fw,index,effect):
  self.fw=fw;self.index=index;self.effect=effect;self.accepted=None
 def __eq__(self,canonical):
  # All coordinates left of the marker are zero, and the head is at marker+1.
  left,right=canonical
  if left!=((1,0,1),)or len(right)<3:return False
  if right[-1]!=('box',('plain',self.effect))or right[-2]!=(1,0,1):return False
  body=right[:-2]
  # All unbounded dependence must be in the final zero gap, coefficient 1.
  if body[-1][0]!=0 or body[-1][1]!=1:return False
  if any(a!=0 for b,a,c in body[:-1]):return False
  pc=''.join(str(b)*c for b,a,c in body[:-1])
  gap_base=len(pc)+body[-1][2]
  if gap_base<40:return False
  outsite=self.fw.decode(pc)
  expected=self.fw.targets[self.index]
  if outsite is None or expected is None:return False
  if self.fw.classes[outsite]!=self.fw.classes[expected]:return False
  site,p,op,r,zero=self.fw.cases[self.index]
  # Prevent a modified machine from stuttering forever among equal classes.
  if op in('CB','CC')and self.fw.rank[outsite]>=self.fw.rank[site]:return False
  self.accepted={'site':outsite,'pc':pc,'gap_base':gap_base,'source_successor':expected,
                 'different_site':outsite!=expected,'jump_rank':self.fw.rank[outsite]}
  return True


def run(args):
 fw=Framework();start=time.monotonic();base=fw.baseline(args.fuel)
 print('BASELINE',base,flush=True)
 states=fw.states;protected=fw.protected;table=fw.table
 protected_targets={table[k][2]for k in protected}
 eligible=[q for q in states if q not in ('96','64')and q not in protected_targets and all((q,b)not in protected for b in(0,1))]
 incoming=defaultdict(list)
 for key,act in table.items():
  if key[0]!=act[2]:incoming[act[2]].append(key)
 result={'scope':'Bounded ranked weak-control-bisimulation instruction contracts; unchanged full frontend; no kernel proof or minimality claim.',
  'baseline':base,'input_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in[BASE/'Prog254.v',BASE/'27-variant-experiments-machine_search-grammar_search-strict_affine.py',BASE/'control_bisim.py',Path(__file__)]},
  'class_counts':fw.counts,'source_sites':len(fw.sites),'action_sites':len(set(fw.closure.values())),'max_jump_rank':max(fw.rank.values()),
  'mode':args.mode,'fuel':args.fuel,'completed':0,'checks':0,'failures':{},'survivors':[],'recipes':[]}
 def check_recipe(dead,other,patch,affected):
  fail=None;reason=None;events=[]
  for _,i in affected:
   ok,_,out=fw.check(patch,i,args.fuel);result['checks']+=1
   if not ok:fail=i;reason=out;break
   if out and out['different_site']:events.append([i,out])
  if fail is None:
   events=[]
   for i in range(len(fw.cases)):
    ok,_,out=fw.check(patch,i,args.fuel);result['checks']+=1
    if not ok:fail=i;reason=out;break
    if out and out['different_site']:events.append([i,out])
  row=[dead,other,fail,reason]
  result['recipes'].append(row);result['completed']+=1
  if fail is None:
   survivor={'deleted':dead,'replacement':other,'different_continuations':events}
   result['survivors'].append(survivor);print('SURVIVOR',survivor,flush=True)
  else:result['failures'][reason]=result['failures'].get(reason,0)+1
 def save():
  result['elapsed_seconds']=time.monotonic()-start
  Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
 if args.mode=='uniform':
  result['planned']=len(eligible)*(len(states)-1)
  for dead in eligible:
   for dest in states:
    if dest==dead:continue
    check_recipe(dead,dest,Patch(table,dead,redirect=dest),fw.usage[dead])
   save()
 elif args.mode=='incoming_actions':
  choices=[q for q in eligible if len(incoming[q])==1 and incoming[q][0]not in protected]
  result['eligible']=choices;result['planned']=len(choices)*4*len(states)
  for dead in choices:
   row=incoming[dead][0]
   for w in (0,1):
    for d in ('L','R'):
     for dest in states+['254']:
      if dest==dead:continue
      action=(w,d,dest)
      check_recipe(dead,[list(row),list(action)],Patch(table,dead,row=row,action=action),fw.row_usage[row])
   save()
 else:raise AssertionError(args.mode)
 result['status']='completed';save()
 print(json.dumps({k:v for k,v in result.items()if k not in('recipes','class_counts','input_sha256')},indent=2),flush=True)

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--mode',choices=['uniform','incoming_actions'],default='uniform')
 ap.add_argument('--fuel',type=int,default=1000)
 ap.add_argument('--output',required=True)
 args=ap.parse_args();assert __debug__ and args.fuel>0
 run(args)
