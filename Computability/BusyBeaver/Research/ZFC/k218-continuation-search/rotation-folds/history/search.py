"""Exploratory folds after certified-source rotations; no parent runtime claim."""
from pathlib import Path
import argparse,collections,gzip,hashlib,itertools,json,sys,time,subprocess,importlib.util,os
sys.dont_write_bytecode=True
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
LIB=ROOT/'Computability/BusyBeaver/Research/ZFC/k218-continuation-search'
def load(n):
 p=LIB/(n+'.py');spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
f=load('filter_source');ck=load('check_joint_fold')

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--seconds',type=int,default=180);a=ap.parse_args();a.out.mkdir();start=time.monotonic();results=[];hits=[];total=0;stop=None
 records=gzip.open(a.out/'rejects.jsonl.gz','wt')
 for seed in ['primary','contextual']:
  directory=Path('/tmp/k218-rotationfold')/seed
  for rotation in json.loads((directory/'census.json').read_text())['rotations']:
   if time.monotonic()-start>=a.seconds:stop='WALL';break
   name=rotation['name'];src=directory/name/'native.tm';old,initial=ck.read(src);Q=sorted({q for q,bit in old});changed={rotation['q'],rotation['r']};assert len(Q)==218
   t=time.monotonic();inv=ck.domain(old,initial,7);cache={};stats=collections.Counter();seen=set();print('LAYOUT',seed,name,'domain',round(time.monotonic()-t,3),flush=True)
   for keep,drop in itertools.permutations(Q,2):
    phi=lambda x:keep if x==drop else x
    actions=[sorted({(old[z,bit][0],old[z,bit][1],phi(old[z,bit][2])) for z in (keep,drop)}) for bit in (0,1)]
    common=[bit for bit in (0,1) if len(actions[bit])==1];affected=bool({keep,drop}&changed)
    if not affected and len(common)!=1:continue
    variants=[]
    if affected:variants += [('inherited',x,y) for x in actions[0] for y in actions[1]]
    if len(common)==1:
     fixed=common[0];other=1-fixed
     targets=sorted((set(Q)|{254})-{drop}) if affected else sorted(changed-{drop})
     for act in itertools.product((0,1),(-1,1),targets):
      pair=[None,None];pair[fixed]=actions[fixed][0];pair[other]=act;variants.append(('changed_pair' if affected else 'changed_helper',*pair))
    if not variants:continue
    new={(q,b):(w,d,phi(z)) for (q,b),(w,d,z) in old.items() if q!=drop}
    for family,act0,act1 in variants:
     if time.monotonic()-start>=a.seconds:stop='WALL';break
     key=(keep,drop,act0,act1)
     if key in seen:continue
     seen.add(key);total+=1;stats['attempts']+=1;stats[family]+=1
     new[keep,0]=act0;new[keep,1]=act1;fail=f.local_filter(old,new,inv,keep,drop,cache,97,7)
     spec=dict(seed=seed,rotation=name,id=total,family=family,keep=keep,drop=drop,rows=[act0,act1])
     if fail is not None:
      stats['filter_rejected']+=1;records.write(json.dumps(dict(**spec,witness=fail),separators=(',',':'))+'\n');continue
     hit=a.out/f'survivor-{total:07d}';hit.mkdir();native=hit/'native.tm';native.write_bytes(f.encode(new,phi(initial)))
     cmd=[sys.executable,'-B',str(LIB/'check_joint_fold.py'),'--old',str(src),'--new',str(native),'--keep',str(keep),'--drop',str(drop),'--radius','7','--fuel','97','--output',str(hit/'relative-proof.json')]
     remaining=a.seconds-(time.monotonic()-start)
     if remaining<=0:stop='WALL';break
     with (hit/'checker.log').open('w') as log:
      try:p=subprocess.run(cmd,stdout=log,stderr=subprocess.STDOUT,timeout=min(remaining,60));code=p.returncode
      except subprocess.TimeoutExpired:code=None
     (hit/'execution.json').write_text(json.dumps(dict(command=cmd,returncode=code,spec=spec),indent=2)+'\n')
     stats['independent_pass' if code==0 else 'independent_fail']+=1
     if code==0:
      proof=json.loads((hit/'relative-proof.json').read_text());assert proof['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS' and proof['new_states']==217 and proof['negative_control']['status']=='REJECTED'
      hits.append(spec);print('RELATIVE_HIT',spec,flush=True);stop='FIRST_RELATIVE_HIT';break
    if stop:break
   results.append(dict(seed=seed,rotation=name,stats=stats,seconds=time.monotonic()-t,domain_contexts=sum(map(len,inv.values()))));print('RESULT',results[-1],flush=True)
   if stop:break
  if stop:break
 records.close();result=dict(status='BOUNDED_FAMILY_COMPLETE' if stop is None else 'STOP_'+stop,rotations=results,total=total,hits=hits,seconds=time.monotonic()-start,radius=7,fuel=97,scope='Inherited/all-target common-branch folds involving either rotated state, plus common-branch folds using a rotated state as helper. Negative filters are incomplete. Rotated218 parents have source/decoder checks only; even relative fold success requires parent runtime and blank initialization before any candidate claim.')
 (a.out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
if __name__=='__main__':main()
