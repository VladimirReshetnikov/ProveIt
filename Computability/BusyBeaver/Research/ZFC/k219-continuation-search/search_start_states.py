"""Universal-domain folds0→q, explicitly changing the initial state toq."""
from pathlib import Path
import argparse,collections,gzip,hashlib,itertools,json,subprocess,sys,time
BASE=Path(__file__).resolve().parent.parent
SHARED=BASE/'k219-continuation-search'
sys.path.insert(0,str(SHARED))
import search_v3 as shared
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 if not __debug__ or sys.flags.optimize:ap.error('Assertions required')
 a.output.mkdir(parents=True,exist_ok=False);started=time.monotonic();deadline=started+115
 inputs=json.loads((SHARED/'inputs.json').read_text());checkerpath=(SHARED/inputs['universal_checker']['path']).resolve()
 ds=inputs['seeds']+[inputs['universal_checker']]
 pins={str((SHARED/d['path']).resolve()):d['sha256'] for d in ds};pins[str(SHARED/'search_v3.py')]='87cd94b5cb8ecc1e1101fbd7cdab5def327632fd289ef6d4e23887f8ff2ad9de'
 assert all(sha(Path(p))==h for p,h in pins.items())
 checker=shared.load_checker(checkerpath)
 # A genuinely changed start is tested independently of the discovery filter.
 control={(q,b):(b,1,1) for q in(0,1) for b in(0,1)};fold={(1,b):(b,1,1) for b in(0,1)}
 cp=checker.check(control,fold,0,1,keep=1,drop=0,radius=2,fuel=9)
 bad=dict(fold);bad[1,0]=(0,1,254)
 try:checker.check(control,bad,0,1,keep=1,drop=0,radius=2,fuel=9)
 except ValueError as e:negative={'status':'REJECTED','reason':str(e)}
 else:raise AssertionError('Invalid changed-start halt accepted')
 dump(a.output/'controls.json',{'positive':cp,'negative':negative,'scope':'Synthetic changed-start API control only.'})
 (a.output/'search.py').write_bytes(Path(__file__).read_bytes());(a.output/'search_v3.py').write_bytes((SHARED/'search_v3.py').read_bytes());(a.output/'checker.py').write_bytes(checkerpath.read_bytes())
 stats=[];hits=[];total=0;stop=None
 with gzip.open(a.output/'rejections.jsonl.gz','wt') as stream:
  for seed in inputs['seeds']:
   oldpath=(SHARED/seed['path']).resolve();old,start=checker.read(oldpath);assert start==0 and len(old)==438
   inv=checker.domain(old,start,7);cache={};states=sorted({q for q,b in old}-{0})
   assert len(states)==218
   rows=[]
   for keep in states:
    phi=lambda q:keep if q==0 else q
    choices=[sorted({(old[q,b][0],old[q,b][1],phi(old[q,b][2])) for q in(keep,0)}) for b in(0,1)]
    common=[b for b in(0,1) if len(choices[b])==1]
    variants=[('inherited',x,y) for x in choices[0] for y in choices[1]]
    if len(common)==1:
     fixed=common[0];other=1-fixed
     for act in itertools.product((0,1),(-1,1),sorted(set(states)|{254})):
      if act in choices[other]:continue
      pair=[None,None];pair[fixed]=choices[fixed][0];pair[other]=act
      variants.append(('one_common_branch',*pair))
    rows.append({'keep':keep,'candidate_count':len(variants),'attempted':0,'filter_rejections':0,'checker_rejections':0,'certificates':0,'status':'NOT_STARTED','variants':variants})
   summary={'seed':seed['name'],'candidate_count':sum(r['candidate_count'] for r in rows),'states':rows}
   stats.append(summary)
   for row in rows:
    keep=row['keep'];phi=lambda q:keep if q==0 else q
    new={(q,b):(w,d,phi(z)) for(q,b),(w,d,z) in old.items() if q!=0}
    row['status']='RUNNING'
    for family,a0,a1 in row['variants']:
     if time.monotonic()>=deadline:stop='TIME_LIMIT';break
     total+=1;row['attempted']+=1;new[keep,0]=a0;new[keep,1]=a1
     candidate={'id':total,'seed':seed['name'],'family':family,'keep':keep,'drop':0,'new_start':keep,'rows':[list(a0),list(a1)]}
     failure=shared.local_filter(old,new,inv,keep,0,cache,fuel=97,radius=7)
     if failure is not None:
      row['filter_rejections']+=1;stream.write(json.dumps({**candidate,'witness':failure},separators=(',',':'))+'\n');continue
     hit=a.output/f'survivor-{total:06d}';hit.mkdir();native=hit/'candidate.native.tm';native.write_bytes(shared.encode(new,keep));assert checker.read(native)[1]==keep
     command=[sys.executable,'-B',str(checkerpath),'--old',str(oldpath),'--new',str(native),'--keep',str(keep),'--drop','0','--radius','7','--fuel','97','--output',str(hit/'certificate.json')]
     remaining=deadline-time.monotonic()
     if remaining<=0:stop='TIME_LIMIT';break
     tick=time.monotonic()
     with (hit/'checker.log').open('w') as log:
      try:r=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=remaining);code=r.returncode;timedout=False
      except subprocess.TimeoutExpired:code=None;timedout=True
     dump(hit/'execution.json',{'command':command,'exit_code':code,'timed_out':timedout,'seconds':time.monotonic()-tick})
     if code==0:
      proof=json.loads((hit/'certificate.json').read_text());assert proof['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS' and proof['start_old']==0 and proof['start_new']==keep and proof['new_states']==218 and proof['negative_control']['status']=='REJECTED'
      row['certificates']+=1;hits.append({**candidate,'path':str(hit),'native_sha256':sha(native)});print(json.dumps({'CERTIFIED_START_FOLD':hits[-1]}),flush=True)
     else:row['checker_rejections']+=1
    row['status']='COMPLETE' if row['attempted']==row['candidate_count'] else 'INCOMPLETE_TIME_LIMIT'
    if stop:break
   if stop:break
 for seed in stats:
  for row in seed['states']:del row['variants']
 assert all(sha(Path(p))==h for p,h in pins.items())
 result={'status':'COMPLETE_START_FOLD_SEARCH' if stop is None else 'INCOMPLETE_'+stop,'seconds':time.monotonic()-started,'attempted':total,'hits':hits,'seeds':stats,'inputs':pins,'source_sha256':sha(Path(__file__)),'rejections_sha256':sha(a.output/'rejections.jsonl.gz'),'radius':7,'fuel':97,'limits':{'internal_seconds':115,'external_seconds':120},'scope':'Every q≠0 on each seed; inherited or one-common-branch synthesis only. Quotient0→q changes native start toq. Original all-initial-tape invariant; independent checker required for survivors. Bounded failures are not semantic counterexamples or a lower bound.'}
 dump(a.output/'result.json',result);print(json.dumps({k:v for k,v in result.items() if k not in('inputs','seeds')},indent=2))
if __name__=='__main__':main()
