#!/usr/bin/env python3
"""Bounded discovery of inherited-action shifted-head folds; no acceptance without independent replay."""
from pathlib import Path
import argparse,gzip,hashlib,importlib.util,itertools,json,subprocess,sys,time
CHECKER=Path(__file__).with_name('check_shifted.py')
CHECKER_SHA='5d8ca0b4bed565fbfcf91164a1e4462b139c7e3d502f68236f21e48703c0c2c9'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def encode(t,start):return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()
def load():
 assert sha(CHECKER)==CHECKER_SHA
 sp=importlib.util.spec_from_file_location('independent_shifted_checker',CHECKER);c=importlib.util.module_from_spec(sp);sp.loader.exec_module(c);return c

def filt(old,new,inv,keep,drop,delta,cache,deadline,radius=7,fuel=97):
 """Only keep/drop need explicit joins; all other rows are checked exact mapped one-step copies by builder."""
 phi=lambda q:keep if q==drop else q
 off=lambda q:delta if q==drop else 0
 for q in (drop,keep):
  for bit in (0,1):
   w,d,z=old[q,bit]
   if q!=drop and new[q,bit]==(w,d+off(z),phi(z)):continue
   key=('words',q,bit)
   if key not in cache:
    ws=sorted(m for m in inv[q]if(m>>radius)&1==bit)
    if len(ws)>2:ws=[ws[0],ws[-1],*ws[1:-1]]
    cache[key]=ws
   for idx,word in enumerate(cache[key]):
    if idx%128==0 and time.monotonic()>deadline:raise TimeoutError('discovery deadline')
    key=q,word
    if key not in cache:
     oq,oh,om=q,0,word;path=[]
     for _ in range(fuel):
      if oq==254 or not -radius<=oh<=radius:break
      ob=(om>>(oh+radius))&1;ow,od,oq=old[oq,ob];om=(om&~(1<<(oh+radius)))|(ow<<(oh+radius));oh+=od;path.append((oq,oh,om))
     cache[key]=path
    # The old path is reusable; candidate-dependent mapping is always fresh.
    path=cache[key];goals={(phi(oq),oh+off(oq),om)for oq,oh,om in path};oldhalt=any(oq==254 for oq,_,_ in path)
    nq,nh,nm=phi(q),off(q),word;seen=set();joined=False;reason='fuel'
    for step in range(1,fuel+1):
     if not -radius<=nh<=radius:reason='new_window_exit';break
     key=nq,nh,nm
     if key in seen:reason='new_cycle';break
     seen.add(key);nb=(nm>>(nh+radius))&1;nw,nd,nq=new[nq,nb];nm=(nm&~(1<<(nh+radius)))|(nw<<(nh+radius));nh+=nd
     if nq==254:joined=oldhalt;reason='unmatched_halt';break
     if(nq,nh,nm)in goals:joined=True;break
    if not joined:return {'row':[q,bit],'window':word,'reason':reason}
 return None

def families(old,start):
 Q=sorted({q for q,b in old});incoming={q:[]for q in Q}
 for k,(w,d,z)in old.items():
  if z in incoming:incoming[z].append((k,d))
 for drop in Q:
  if drop==start:continue
  for keep in Q:
   if keep==drop:continue
   dirs={d for(q,b),d in incoming[drop]if q not in(keep,drop)}
   for delta in(-2,2):
    if dirs and dirs!={-delta//2}:continue
    phi=lambda q:keep if q==drop else q
    new={}
    for(q,b),(w,d,z)in old.items():
     if q==drop:continue
     nd=d+delta if z==drop else d
     # Keep rows are replaced next, including otherwise invalid mapped motion.
     if q!=keep:assert nd in(-1,1)
     new[q,b]=(w,nd,phi(z))
    actions=[]
    for bit in(0,1):
     aset=set()
     for q in(keep,drop):
      w,d,z=old[q,bit];aset.add((w,d,phi(z)))
      if z==drop and d+delta in(-1,1):aset.add((w,d+delta,keep))
     actions.append(sorted(aset))
    for a0,a1 in itertools.product(*actions):
     new[keep,0]=a0;new[keep,1]=a1
     yield keep,drop,delta,a0,a1,new,len(actions[0])*len(actions[1])

def controls(c):
 O={(0,0):(0,1,2),(0,1):(1,1,1),(1,0):(0,1,4),(1,1):(1,1,4),(4,0):(0,1,5),(4,1):(1,1,5),(5,0):(0,1,3),(5,1):(1,1,3),(2,0):(0,1,3),(2,1):(1,1,3),(3,0):(0,1,3),(3,1):(1,1,254)}
 rows=[]
 for sign in(1,-1):
  old={k:(w,d*sign,z)for k,(w,d,z)in O.items()};new={k:v for k,v in old.items()if k[0]!=2};new[0,0]=(0,-sign,1)
  inv=c.base.domain(old,0,3);assert filt(old,new,inv,1,2,-2*sign,{},time.monotonic()+10,3,97)is None
  found=any((k,d,delta)==(1,2,-2*sign)and n==new for k,d,delta,a,b,n,num in families(old,0));assert found
  rows.append({'sign':sign,'positive_filter':True,'positive_family_member':found})
 return rows

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--name',required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--seconds',type=int,default=110);a=ap.parse_args()
 assert __debug__ and 1<=a.seconds<=110
 a.output.mkdir(parents=True,exist_ok=False);c=load();control=controls(c);old,start=c.base.read(a.table);assert len(old)==438
 oldsha=sha(a.table);(a.output/'old.tm').write_bytes(a.table.read_bytes());(a.output/'search.py').write_bytes(Path(__file__).read_bytes());(a.output/'check_shifted.py').write_bytes(CHECKER.read_bytes())
 begun=time.monotonic();deadline=begun+a.seconds;inv=c.base.domain(old,start,7);cache={};attempted=0;rejected=0;survivors=[];stop=None;pairs=set();bydrop={};finished={};expected={}
 with gzip.open(a.output/'rejections.jsonl.gz','wt')as log:
  try:
   for keep,drop,delta,a0,a1,new,group_size in families(old,start):
    if time.monotonic()>deadline:stop='DEADLINE';break
    attempted+=1;pair=(keep,drop,delta);pairs.add(pair);expected[pair]=group_size;bydrop[drop]=bydrop.get(drop,0)+1
    desc={'id':attempted,'keep':keep,'drop':drop,'shift':delta,'actions':[a0,a1]}
    f=filt(old,new,inv,keep,drop,delta,cache,deadline)
    if f is not None:
     rejected+=1;finished[pair]=finished.get(pair,0)+1;log.write(json.dumps({**desc,'failure':f},separators=(',',':'))+'\n');continue
    d=a.output/f'survivor-{attempted}';d.mkdir();p=d/'candidate.native.tm';p.write_bytes(encode(new,start))
    cmd=[sys.executable,'-B',str(CHECKER),'--old',str(a.table),'--new',str(p),'--keep',str(keep),'--drop',str(drop),'--shift',str(delta),'--radius','7','--fuel','97','--output',str(d/'independent.json')]
    t=time.monotonic();remaining=deadline-t
    with(d/'independent.log').open('w')as out:
     try:rc=subprocess.run(cmd,stdout=out,stderr=subprocess.STDOUT,timeout=max(.1,remaining)).returncode;timeout=False
     except subprocess.TimeoutExpired:rc=None;timeout=True
    e={**desc,'command':cmd,'exit_code':rc,'timeout':timeout,'seconds':time.monotonic()-t};dump(d/'execution.json',e);survivors.append(e);finished[pair]=finished.get(pair,0)+1
    if rc==0:
     r=json.loads((d/'independent.json').read_text());assert r['status']=='ALL_TAPE_SHIFTED_JOINT_DIAGRAM_PASS'and r['new_states']==218
     print('CERTIFIED218',str(d),flush=True);stop='CERTIFIED_SURVIVOR';break
    if timeout:stop='DEADLINE';break
  except TimeoutError:stop='DEADLINE_IN_CANDIDATE'
 assert sha(a.table)==oldsha and sha(CHECKER)==CHECKER_SHA
 result={'status':'COMPLETE_BOUNDED_FAMILY'if stop is None else'INCOMPLETE_'+stop,'name':a.name,'old_sha256':oldsha,'checker_sha256':CHECKER_SHA,'search_sha256':sha(__file__),'seconds':time.monotonic()-begun,'wall_limit':a.seconds,'radius':7,'fuel':97,'states':219,'eligible_pair_shifts_visited':len(pairs),'completed_pair_shifts':sum(finished.get(k,0)==v for k,v in expected.items()),'partial_pair_shifts':[{'keep':k[0],'drop':k[1],'shift':k[2],'finished_candidates':finished.get(k,0),'expected_candidates':v}for k,v in expected.items()if finished.get(k,0)!=v],'attempted':attempted,'filter_rejected':rejected,'attempted_by_drop':bydrop,'survivors':survivors,'controls':control,'domain_contexts':sum(len(v)for q,v in inv.items()if q!=254),'scope':'Inherited keep/drop actions plus valid one-step target-offset versions. All noninitial drops, all distinct keeps including start. Other incoming rows flip their common direction. Rejection only means bounded positive diagram unavailable in an overapproximation, not semantic inequivalence or minimality. Acceptance requires independent checker recomputation of the full domain.'}
 dump(a.output/'result.json',result);print(json.dumps(result,sort_keys=True),flush=True)
if __name__=='__main__':main()
