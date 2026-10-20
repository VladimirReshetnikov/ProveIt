#!/usr/bin/env python3
"""Probe the known left marker while merging198 into66. Bounded discovery only."""
from pathlib import Path
import argparse,gzip,hashlib,itertools,json,os,subprocess,sys,time
import search_v3 as shared
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 if not __debug__ or sys.flags.optimize:ap.error('Assertions required')
 a.output.mkdir(parents=True,exist_ok=False)
 inputs=json.loads((P/'inputs.json').read_text());ds=inputs['seeds']+[inputs['decoder_allocation'],inputs['universal_checker']]
 pins={str((P/d['path']).resolve()):d['sha256'] for d in ds}
 assert all(sha(Path(p))==h for p,h in pins.items())
 cp=(P/inputs['universal_checker']['path']).resolve();checker=shared.load_checker(cp)
 for f in (Path(__file__),P/'search_v3.py',cp):(a.output/f.name).write_bytes(f.read_bytes())
 started=time.monotonic();allresults=[];total=0;hits=[];stop=None
 with gzip.open(a.output/'rejections.jsonl.gz','wt') as rejected:
  for sd in inputs['seeds']:
   path=(P/sd['path']).resolve();old,start=checker.read(path);assert len(old)==438 and start==0
   inv=checker.domain(old,start,7)
   assert all((w>>6)&1==0 and (w>>5)&1==1 for w in inv[66])
   assert all((w>>6)&1==1 and (w>>5)&1==0 for w in inv[198])
   new={(q,b):(w,d,66 if z==198 else z) for(q,b),(w,d,z) in old.items() if q!=198}
   targets=sorted({q for q,b in new}|{254});assert len(targets)==219
   cache={};stats={'seed':sd['name'],'attempted':0,'filter_rejections':0,'full_checker_rejections':0,'full_checker_pass':0}
   for z0,z1 in itertools.product(targets,repeat=2):
    if time.monotonic()-started>=120:stop='TIME_LIMIT';break
    total+=1;stats['attempted']+=1;new[66,0]=(1,-1,z0);new[66,1]=(1,-1,z1)
    spec={'id':total,'seed':sd['name'],'keep':66,'drop':198,'rows':[[1,-1,z0],[1,-1,z1]]}
    fail=shared.local_filter(old,new,inv,66,198,cache,97,7)
    if fail is not None:
     stats['filter_rejections']+=1;rejected.write(json.dumps({**spec,'stage':'bounded_filter','witness':fail},separators=(',',':'))+'\n');continue
    d=a.output/f'survivor-{total:06d}';d.mkdir();native=d/'candidate.native.tm';native.write_bytes(shared.encode(new,start))
    command=[sys.executable,'-B',str(cp),'--old',str(path),'--new',str(native),'--keep','66','--drop','198','--radius','7','--fuel','97','--output',str(d/'proof.json')]
    remaining=120-(time.monotonic()-started)
    if remaining<=0:stop='TIME_LIMIT';break
    with (d/'checker.log').open('w') as log:
     try:run=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=min(120,remaining),env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'));code=run.returncode;timed=False
     except subprocess.TimeoutExpired:code=None;timed=True
    dump(d/'execution.json',{'command':command,'exit_code':code,'timed_out':timed,'candidate':spec})
    if code!=0:
     stats['full_checker_rejections']+=1;rejected.write(json.dumps({**spec,'stage':'full_checker','record':str(d/'execution.json')},separators=(',',':'))+'\n');continue
    proof=json.loads((d/'proof.json').read_text());assert proof['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS' and proof['negative_control']['status']=='REJECTED' and proof['new_states']==218 and proof['old_states']==219
    stats['full_checker_pass']+=1;hits.append({**spec,'proof':str(d/'proof.json'),'native_sha256':sha(native)})
    if len(hits)==4:stop='HIT_LIMIT';break
   allresults.append(stats)
   if stop:break
 assert all(sha(Path(p))==h for p,h in pins.items())
 result={'status':'COMPLETE_BOUNDED_SEARCH' if stop is None else 'INCOMPLETE_'+stop,'inputs':pins,'source_sha256':sha(Path(__file__)),'shared_filter_sha256':sha(P/'search_v3.py'),'seconds':time.monotonic()-started,'attempted':total,'seeds':allresults,'hits':hits,'family':'198 maps to66; both merged branches write1/moveLeft, with all219 remaining-state/halt targets independently chosen. Otherrows are mapped unchanged.','radius':7,'fuel':97,'maximum_specifications':95922,'shared_wall_seconds':120,'entry_window_invariants':'66 has left0/second-left1;198 has left1/second-left0, checked throughout the inductive all-initial-tape window domain.','rejections_sha256':sha(a.output/'rejections.jsonl.gz'),'scope':'Bounded-filter failures are not semantic counterexamples or a lower bound. Only full-checker successes would establish relative all-initial-tape equivalence; no such success is assumed.'}
 dump(a.output/'result.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
