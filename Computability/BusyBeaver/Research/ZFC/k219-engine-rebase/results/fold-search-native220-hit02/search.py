#!/usr/bin/env python3
"""Bounded fold discovery on newly allocated tables, never their acceptance gate.

Uses the preserved Drop v3 local filter and unchanged Source139 checker.
These tables have separately pending primitive runtime/startup obligations.
"""
from pathlib import Path
import argparse,hashlib,itertools,json,sys,time
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--table',type=Path,required=True);ap.add_argument('--sha',required=True);ap.add_argument('--out',type=Path,required=True)
 a=ap.parse_args();assert __debug__ and not sys.flags.optimize;assert not a.out.exists();assert sha(a.table)==a.sha
 deps={'check_joint_fold.py':'82d0b364dfdbc7433a58c3c3e7166ec6a32ac9268e0e516f5f113f1287f44031','original_search_v3.py':'87cd94b5cb8ecc1e1101fbd7cdab5def327632fd289ef6d4e23887f8ff2ad9de'}
 assert all(sha(HERE/'code'/p)==h for p,h in deps.items())
 sys.dont_write_bytecode=True;sys.path.insert(0,str(HERE/'code'))
 import check_joint_fold as c,original_search_v3 as f
 old,start=c.read(a.table);assert len(old)==438
 started=time.monotonic();inv=c.domain(old,start,5);paths={};Q={q for q,b in old};states=sorted(Q-{0,84})
 a.out.mkdir(parents=True);(a.out/'search.py').write_bytes(Path(__file__).read_bytes())
 attempted=0;examples=[];survivors=[];stop=None
 for keep,drop in itertools.combinations(states,2):
  phi=lambda q:keep if q==drop else q
  new={(q,b):(w,d,phi(z)) for (q,b),(w,d,z) in old.items() if q!=drop}
  actions=[sorted({(old[q,b][0],old[q,b][1],phi(old[q,b][2])) for q in (keep,drop)}) for b in (0,1)]
  common=[b for b in (0,1) if len(actions[b])==1]
  variants=[('inherited',a0,a1) for a0 in actions[0] for a1 in actions[1]]
  if len(common)==1:
   fixed=common[0];other=1-fixed
   for act in itertools.product((0,1),(-1,1),sorted(Q-{drop}|{254})):
    if act in actions[other]:continue
    pair=[None,None];pair[fixed]=actions[fixed][0];pair[other]=act
    variants.append(('one-branch-helper',*pair))
  for family,a0,a1 in variants:
   if attempted>=350000 or time.monotonic()-started>=180:stop='DISCOVERY_BOUND';break
   attempted+=1;new[keep,0]=a0;new[keep,1]=a1
   failure=f.local_filter(old,new,inv,keep,drop,paths,97,5)
   if failure is not None:
    if len(examples)<10:examples.append(dict(keep=keep,drop=drop,family=family,rows=[a0,a1],failure=failure))
    continue
   d=a.out/f'survivor-{attempted:06d}';d.mkdir();(d/'candidate.native.tm').write_bytes(f.encode(new,start))
   item=dict(keep=keep,drop=drop,family=family,rows=[a0,a1],candidate_sha256=sha(d/'candidate.native.tm'))
   try:
    proof=c.check(old,new,start,start,keep,drop,5,97,inv)
    bad=new.copy();bad[start,0]=(0,1,254)
    try:c.check(old,bad,start,start,keep,drop,5,97,inv)
    except ValueError as exc:proof['negative_control']=str(exc)
    else:raise AssertionError('Negative control accepted')
    dump(d/'relative-proof.json',proof);item['status']='RELATIVE_ALL_INITIAL_TAPE_FOLD_PASS'
   except ValueError as exc:item.update(status='UNCHANGED_CHECKER_REJECTED',error=str(exc))
   dump(d/'result.json',item);survivors.append(item);print(json.dumps(item),flush=True)
   if item['status']=='RELATIVE_ALL_INITIAL_TAPE_FOLD_PASS':stop='FIRST_RELATIVE_PASS';break
  if stop:break
 assert sha(a.table)==a.sha
 dump(a.out/'result.json',dict(status='COMPLETE_BOUNDED_FAMILY' if stop is None else stop,old_sha256=a.sha,old_path=str(a.table.resolve()),attempted=attempted,seconds=time.monotonic()-started,dependencies=deps,negative_examples=examples,survivors=survivors,radius=5,fuel=97,scope='All pairs excluding native start0 and dispatcher84; inherited actions and all one-branch helper actions when the other branch agrees. Discovery filter is incomplete. Any checker pass is only relative to this possibly unverified raw source allocation.'))
 print('DONE',attempted,stop,len(survivors),flush=True)
if __name__=='__main__':main()
