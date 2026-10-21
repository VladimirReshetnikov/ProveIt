#!/usr/bin/env python3
"""Bounded full-state inherited/one-common-action folds of an exact K218 seed.

The unchanged reviewed K219 local filter caches old paths only. All ordered
keep/drop pairs, including the initial state, are enumerated. Only a separate
fresh-domain Source139 checker can accept a candidate. A rejection is an
incomplete finite-window diagram failure, not a semantic counterexample.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,itertools,json,gzip,time,subprocess,sys,os
HERE=Path(__file__).resolve().parent
PINS={'filter_source.py':'87cd94b5cb8ecc1e1101fbd7cdab5def327632fd289ef6d4e23887f8ff2ad9de','check_joint_fold.py':'82d0b364dfdbc7433a58c3c3e7166ec6a32ac9268e0e516f5f113f1287f44031'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(name):
 p=HERE/(name+'.py');s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--seed',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--seconds',type=int,default=110);a=ap.parse_args()
 assert __debug__ and not os.getenv('PYTHONOPTIMIZE') and 1<=a.seconds<=110
 assert digest(a.seed) == '0b2ec7ca3440d3afac79d5d3b05dd18f1b2db0db185e85e8894a666cae046eeb'
 assert all(digest(HERE/n)==h for n,h in PINS.items())
 filt=load('filter_source');check=load('check_joint_fold')
 a.output.mkdir(parents=True,exist_ok=False);started=time.monotonic();old,start=check.read(a.seed);Q=sorted({q for q,b in old});assert len(Q)==217 and len(old)==434
 inputs={str(p.resolve()):digest(p)for p in [a.seed,Path(__file__),HERE/'filter_source.py',HERE/'check_joint_fold.py']};dump(a.output/'inputs.json',inputs)
 I=check.domain(old,start,7);paths={};stats={'attempted':0,'completed_pairs':0,'started_pairs':0,'total_ordered_pairs':len(Q)*(len(Q)-1),'inherited':0,'one_common_action':0,'filter_rejected':0,'independent_rejected':0,'independent_pass':0,'independent_incomplete':0};hits=[];stop=None;pending=None;witnesses=gzip.open(a.output/'rejections.jsonl.gz','wt')
 try:
  for keep,drop in itertools.permutations(Q,2):
   if time.monotonic()-started>=a.seconds:stop='WALL_LIMIT';break
   stats['started_pairs']+=1;phi=lambda q:keep if q==drop else q
   new={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=drop};newstart=phi(start)
   actions=[sorted({(old[q,b][0],old[q,b][1],phi(old[q,b][2]))for q in (keep,drop)})for b in(0,1)]
   common=[b for b in(0,1)if len(actions[b])==1]
   variants=[('inherited',a0,a1)for a0 in actions[0]for a1 in actions[1]]
   if len(common)==1:
    fixed=common[0];other=1-fixed
    for action in itertools.product((0,1),(-1,1),sorted(set(Q)-{drop}|{254})):
     if action in actions[other]:continue
     pair=[None,None];pair[fixed]=actions[fixed][0];pair[other]=action;variants.append(('one_common_action',*pair))
   for family,a0,a1 in variants:
    if time.monotonic()-started>=a.seconds:stop='WALL_LIMIT';break
    stats['attempted']+=1;stats[family]+=1;new[keep,0]=a0;new[keep,1]=a1
    spec={'id':stats['attempted'],'keep':keep,'drop':drop,'start':newstart,'family':family,'rows':[a0,a1]};pending=spec
    fail=filt.local_filter(old,new,I,keep,drop,paths,97,7)
    if fail is not None:
     stats['filter_rejected']+=1;witnesses.write(json.dumps({**spec,'stage':'bounded_filter','witness':fail},separators=(',',':'))+'\n');pending=None;continue
    hd=a.output/f'survivor-{stats["attempted"]:07d}';hd.mkdir();native=hd/'candidate.native.tm';native.write_bytes(filt.encode(new,newstart))
    command=[sys.executable,'-B',str(HERE/'check_joint_fold.py'),'--old',str(a.seed),'--new',str(native),'--keep',str(keep),'--drop',str(drop),'--radius','7','--fuel','97','--output',str(hd/'universal.json')]
    remaining=a.seconds-(time.monotonic()-started)
    if remaining<=0:stats['independent_incomplete']+=1;stop='WALL_LIMIT';break
    t=time.monotonic()
    with (hd/'universal.log').open('w')as log:
     try:r=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=min(120,remaining),env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'});code=r.returncode;timed=False
     except subprocess.TimeoutExpired:code=None;timed=True
    dump(hd/'execution.json',{'command':command,'exit_code':code,'timed_out':timed,'seconds':time.monotonic()-t,'candidate':spec})
    if timed:stats['independent_incomplete']+=1;stop='WALL_LIMIT';break
    if code!=0:stats['independent_rejected']+=1;witnesses.write(json.dumps({**spec,'stage':'independent_checker','record':str(hd/'execution.json')})+'\n');pending=None;continue
    proof=json.loads((hd/'universal.json').read_text());assert proof['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'and proof['old_states']==217 and proof['new_states']==216 and proof['negative_control']['status']=='REJECTED'
    stats['independent_pass']+=1;hits.append({**spec,'native_sha256':digest(native),'proof':str(hd/'universal.json')});pending=None;dump(a.output/'hits.json',hits)
    print('INDEPENDENT_216_PASS',json.dumps(hits[-1]),flush=True);stop='FIRST_VERIFIED_SURVIVOR';break
   if stop:break
   stats['completed_pairs']+=1
   if stats['completed_pairs']%5000==0:print('PROGRESS',stats['completed_pairs'],stats['attempted'],round(time.monotonic()-started,2),flush=True)
 finally:witnesses.close()
 assert inputs=={p:digest(Path(p))for p in inputs}
 assert stats['attempted']==stats['filter_rejected']+stats['independent_rejected']+stats['independent_pass']+stats['independent_incomplete']
 result={'status':'COMPLETE_BOUNDED_SEARCH'if stop is None else'INCOMPLETE_'+stop,'stop':stop,'stats':stats,'hits':hits,'pending':pending,'seconds':time.monotonic()-started,'bounds':{'radius':7,'fuel':97,'soft_seconds':a.seconds,'external_seconds':120},'inputs':inputs,'domain_contexts':sum(len(I[q])for q in Q),'rejections_sha256':digest(a.output/'rejections.jsonl.gz'),'scope':'Every ordered pair of distinct working states, including the initial state. Inherited keeper/drop action choices, plus all writes/moves/remaining-targets for one action when the other mapped action agrees. Other rows are mapped exact copies. Negative filter outcomes are incomplete proof-search failures, not semantic counterexamples or lower bounds. Only separate fresh-domain checker successes are accepted; neither source reallocation nor a proof assistant is part of this search.'}
 dump(a.output/'result.json',result);print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
