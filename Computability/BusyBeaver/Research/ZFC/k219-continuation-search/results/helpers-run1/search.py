#!/usr/bin/env python3
"""Bounded folds involving K219 new/shared helpers 302, 301 or 108.

The fast finite-window join filter is only a discovery filter. Every retained
candidate is independently passed through the unchanged Source139 universal
checker, including its initial-halt negative control. No failed join is claimed
to be a semantic counterexample or a state lower bound.
"""
from pathlib import Path
import argparse,collections,gzip,hashlib,importlib.util,itertools,json,os,subprocess,sys,time

ROOT=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def encode(t,start=0):
 return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(t.items()))).encode()
def load_checker(path):
 spec=importlib.util.spec_from_file_location('k219_existing_universal_checker',path)
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def local_filter(old,new,invariant,keep,drop,old_paths,fuel=9,radius=3):
 """Compare only the four potentially nonidentical rows of the state fold.

 All other rows are syntactically mapped copies. Failure means only that this
 bounded diagram was not found in this overapproximating window domain.
 """
 phi=lambda q:keep if q==drop else q
 for q in (keep,drop):
  for bit in (0,1):
   w,d,z=old[q,bit]
   if new[keep,bit]==(w,d,phi(z)):continue
   pattern_key=('patterns',q,bit)
   if pattern_key not in old_paths:
    patterns=sorted(m for m in invariant[q] if ((m>>radius)&1)==bit)
    if len(patterns)>2:patterns=[patterns[0],patterns[-1],*patterns[1:-1]]
    old_paths[pattern_key]=patterns
   patterns=old_paths[pattern_key]
   for word in patterns:
    key=(q,word)
    if key not in old_paths:
     oq,oh,om=q,0,word;path=[]
     for tick in range(1,fuel+1):
      if oq==254 or not -radius<=oh<=radius:break
      ob=(om>>(oh+radius))&1;ow,od,oq=old[oq,ob]
      om=(om&~(1<<(oh+radius)))|(ow<<(oh+radius));oh+=od
      path.append((oq,oh,om))
     old_paths[key]=path
    path=old_paths[key];goals={(phi(oq),oh,om) for oq,oh,om in path}
    old_halts=any(oq==254 for oq,oh,om in path)
    nq,nh,nm=keep,0,word;visited=set();joined=False
    reason='no_join_within_filter_fuel'
    for tick in range(1,fuel+1):
     if nq==254 or not -radius<=nh<=radius:
      reason='new_exits_window_before_join';break
     state=(nq,nh,nm)
     if state in visited:reason='new_repeats_before_join';break
     visited.add(state)
     nb=(nm>>(nh+radius))&1;nw,nd,nq=new[nq,nb]
     nm=(nm&~(1<<(nh+radius)))|(nw<<(nh+radius));nh+=nd
     if nq==254:
      joined=old_halts;reason='new_halt_without_old_halt';break
     if (nq,nh,nm) in goals:joined=True;break
    if not joined:return {'old_row':[q,bit],'window':word,'radius':radius,'fuel':fuel,'reason':reason}
 return None

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--seconds',type=int,default=1200)
 ap.add_argument('--max-candidates',type=int,default=350000)
 ap.add_argument('--filter-radius',type=int,choices=(3,5,7),default=7)
 ap.add_argument('--filter-fuel',type=int,choices=(9,97),default=97)
 a=ap.parse_args()
 if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):ap.error('Assertions must be enabled')
 if not 1<=a.seconds<=1200 or not 1<=a.max_candidates<=350000:ap.error('Bounds may only be narrowed')
 output=a.output.resolve();output.mkdir(parents=True,exist_ok=False)
 inputs=json.loads((ROOT/'inputs.json').read_text());descriptors=inputs['seeds']+[inputs['decoder_allocation'],inputs['universal_checker']]
 for d in descriptors:
  p=(ROOT/d['path']).resolve();assert digest(p)==d['sha256'],str(p)
 before={str((ROOT/d['path']).resolve()):d['sha256'] for d in descriptors}
 checker_path=(ROOT/inputs['universal_checker']['path']).resolve();checker=load_checker(checker_path)
 decoder_states=sorted(map(int,json.loads((ROOT/inputs['decoder_allocation']['path']).read_text())))
 assert len(decoder_states)==169 and 0 not in decoder_states
 dump(output/'inputs.json',inputs)
 (output/'search.py').write_bytes(Path(__file__).read_bytes())
 (output/'check_joint_fold.py').write_bytes(checker_path.read_bytes())
 started=time.monotonic();total=0;allstats=[];hits=[];stop=None
 failures=gzip.open(output/'rejections.jsonl.gz','wt',encoding='utf8')
 def reject(x):failures.write(json.dumps(x,separators=(',',':'))+'\n')
 try:
  for sd in inputs['seeds']:
   oldpath=(ROOT/sd['path']).resolve();old,start=checker.read(oldpath)
   assert len(old)==438 and {q for q,b in old}>=set(decoder_states)
   working_states={q for q,b in old};anchors=(302,301,108)
   assert set(anchors)<=working_states and start not in anchors
   pairs=sorted({tuple(sorted((anchor,q))) for anchor in anchors for q in working_states-{start,anchor}})
   assert len(pairs)==648
   inv=checker.domain(old,start,a.filter_radius);paths={};stats={'seed':sd['name'],'attempted':0,'families':{},'filter_rejections':0,'universal_rejections':0,'universal_pass':0,'pairs':0,'matched_branch_pairs':0};allstats.append(stats)
   for keep,drop in pairs:
    stats['pairs']+=1;phi=lambda q:keep if q==drop else q
    new={(q,b):(w,d,phi(z)) for (q,b),(w,d,z) in old.items() if q!=drop}
    actions=[sorted({(old[q,b][0],old[q,b][1],phi(old[q,b][2])) for q in (keep,drop)}) for b in (0,1)]
    common=[b for b in (0,1) if len(actions[b])==1]
    if common:stats['matched_branch_pairs']+=1
    variants=[('inherited',a0,a1) for a0 in actions[0] for a1 in actions[1]]
    # Synthesize the other action over every write/move/remaining target.
    # No source/engine rows outside the retained merged state are altered.
    if len(common)==1:
     fixed=common[0];other=1-fixed;targets=sorted({q for q,b in new}|{254})
     for w,d,z in itertools.product((0,1),(-1,1),targets):
      act=(w,d,z)
      if act in actions[other]:continue
      pair=[None,None];pair[fixed]=actions[fixed][0];pair[other]=act
      variants.append(('tag_helper',pair[0],pair[1]))
    for family,a0,a1 in variants:
     if total>=a.max_candidates:stop='CANDIDATE_LIMIT';break
     if time.monotonic()-started>=a.seconds:stop='TIME_LIMIT';break
     total+=1;stats['attempted']+=1;stats['families'][family]=stats['families'].get(family,0)+1
     new[keep,0]=a0;new[keep,1]=a1
     candidate={'seed':sd['name'],'id':total,'family':family,'keep':keep,'drop':drop,'rows':[list(a0),list(a1)]}
     failure=local_filter(old,new,inv,keep,drop,paths,a.filter_fuel,a.filter_radius)
     if failure is not None:
      stats['filter_rejections']+=1;reject({**candidate,'stage':'bounded_filter','witness':failure});continue
     hitdir=output/f'survivor-{total:06d}';hitdir.mkdir()
     native=hitdir/'candidate.native.tm';native.write_bytes(encode(new,start))
     command=[sys.executable,'-B',str(output/'check_joint_fold.py'),'--old',str(oldpath),'--new',str(native),'--keep',str(keep),'--drop',str(drop),'--radius',str(a.filter_radius),'--output',str(hitdir/'universal.json')]
     remaining=a.seconds-(time.monotonic()-started)
     if remaining<=0:stop='TIME_LIMIT';break
     run_start=time.monotonic()
     with (hitdir/'universal.log').open('w') as log:
      try:
       cp=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=min(120,remaining),env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
       code,timed_out=cp.returncode,False
      except subprocess.TimeoutExpired:code,timed_out=None,True
     execution={'command':command,'exit_code':code,'timed_out':timed_out,'seconds':time.monotonic()-run_start,'candidate':candidate};dump(hitdir/'execution.json',execution)
     if code!=0 or timed_out:
      stats['universal_rejections']+=1;reject({**candidate,'stage':'universal_checker','record':str(hitdir/'execution.json')});continue
     proof=json.loads((hitdir/'universal.json').read_text())
     assert proof['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS' and proof['negative_control']['status']=='REJECTED'
     assert proof['new_states']==218 and proof['old_states']==219
     # Canonical graph relabeling keeps all working states; report unreachable.
     order=[start];mp={start:0}
     for q in order:
      for b in (0,1):
       z=new[q,b][2]
       if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
     reachable=len(mp)
     for q in sorted({q for q,b in new}-set(mp)):mp[q]=len(mp)
     mp[254]=218
     canonical={(mp[q],b):(w,d,mp[z]) for (q,b),(w,d,z) in new.items()}
     (hitdir/'candidate.tm').write_bytes(encode(canonical))
     stats['universal_pass']+=1;hits.append({**candidate,'native_sha256':digest(native),'canonical_sha256':digest(hitdir/'candidate.tm'),'graph_reachable_working_states':reachable,'proof':str(hitdir/'universal.json')})
     dump(output/'hits.json',hits)
     if len(hits)>=8:stop='HIT_LIMIT';break
    if stop:break
    if stats['pairs']%1000==0:print(sd['name'],'pairs',stats['pairs'],'candidates',stats['attempted'],'seconds',round(time.monotonic()-started,2),flush=True)
   print('SEED',stats,flush=True)
   if stop:break
 finally:failures.close()
 assert before=={p:digest(Path(p)) for p in before},'Input drift'
 result={'status':'COMPLETE_BOUNDED_SEARCH' if stop is None else 'INCOMPLETE_'+stop,'seconds':time.monotonic()-started,'candidate_limit':a.max_candidates,'wall_limit':a.seconds,'filter_radius':a.filter_radius,'filter_fuel':a.filter_fuel,'anchor_states':[302,301,108],'pair_count_per_seed':648,'attempted':total,'seeds':allstats,'hits':hits,'inputs':before,'search_sha256':digest(Path(__file__)),'rejection_stream_sha256':digest(output/'rejections.jsonl.gz'),'scope':'Two exact certified219 tables; all unordered noninitial working-state pairs involving 302,301 or108; inherited actions and all one-branch tag/helper actions when the other branch already agrees. The explicitly recorded finite-window/fuel filter is incomplete. Only explicitly recorded radius/fuel97 unchanged-checker successes are relative all-initial-tape certificates. No source reassociation, numeric sampling claim, global lower bound or proof-assistant endpoint.'}
 dump(output/'result.json',result);print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
