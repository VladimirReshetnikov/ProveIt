"""Rescreen only first counterwindows removed by the blank-seeded domain.
No blank-relative result is promoted without an independent verifier.
"""
from pathlib import Path
import argparse,collections,gzip,hashlib,json,sys,time
from blank_domain import blank_domain
BASE=Path(__file__).resolve().parent.parent
OWN=BASE/'k219-continuation-search';P=Path(__file__).resolve().parent
sys.path.insert(0,str(OWN))
import search_v3 as shared
import search_hidden_states as hidden
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 if not __debug__ or sys.flags.optimize:raise ValueError('Assertions required')
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--start-run',type=Path,default=OWN/'results/start-states-run1');args=ap.parse_args()
 out=args.output.resolve();out.mkdir(parents=True,exist_ok=False);started=time.monotonic();deadline=started+115
 inputs=json.loads((OWN/'inputs.json').read_text());checkerpath=(OWN/inputs['universal_checker']['path']).resolve();checker=shared.load_checker(checkerpath)
 pins={str((OWN/d['path']).resolve()):d['sha256'] for d in inputs['seeds']+[inputs['universal_checker']]}
 pins[str(OWN/'search_v3.py')]='87cd94b5cb8ecc1e1101fbd7cdab5def327632fd289ef6d4e23887f8ff2ad9de';pins[str(OWN/'search_hidden_states.py')]='48c92b2aaf8b24ec77cbb4f8754a1d5c71e908eafd61eba624b66fff45acb292'
 assert all(sha(Path(p))==h for p,h in pins.items())
 families=[('engine',OWN/'results/engine-helpers-run1','merge'),('dual66',OWN/'results/66-198-run1','merge'),('hidden198',OWN/'results/hidden198-run1','hidden'),('hidden_all',OWN/'results/hidden-states-run1','hidden'),('start',args.start_run.resolve(),'merge')]
 tables={};domains={};caches={};hiddencaches={}
 for seed in inputs['seeds']:
  old,start=checker.read((OWN/seed['path']).resolve());tables[seed['name']]=(old,start);domains[seed['name']]=blank_domain(old,start,7);caches[seed['name']]={}
 stats=[];hits=[];total=0;stop=None
 with gzip.open(out/'rescreened.jsonl.gz','wt') as stream:
  for name,directory,kind in families:
   oldrecord=json.loads((directory/'result.json').read_text());oldstream=directory/'rejections.jsonl.gz'
   expected=oldrecord.get('rejection_stream_sha256',oldrecord.get('rejections_sha256'))
   assert sha(oldstream)==expected
   r={'family':name,'prior_result_sha256':sha(directory/'result.json'),'prior_stream_sha256':expected,'candidate_count':oldrecord['attempted'],'processed':0,'retained_prior_rejection':0,'rescreened':0,'rejected':0,'survivors':0,'status':'RUNNING','per_seed':{}}
   stats.append(r)
   with gzip.open(oldstream,'rt') as previous:
    for line in previous:
     if time.monotonic()>=deadline:stop='TIME_LIMIT';break
     candidate=json.loads(line);seed=candidate['seed'];old,start=tables[seed];domain=domains[seed]
     failure=candidate.get('witness',candidate.get('failure'))
     if kind=='merge':
      q,bit=failure['old_row']
     else:
      q,bit=candidate.get('entry',[66,0])
     r['processed']+=1
     per=r['per_seed'].setdefault(seed,{'processed':0,'retained_prior_rejection':0,'rescreened':0,'rejected':0,'survivors':0})
     per['processed']+=1
     if failure['window'] in domain[q]:
      r['retained_prior_rejection']+=1;per['retained_prior_rejection']+=1;continue
     total+=1;r['rescreened']+=1;per['rescreened']+=1
     if kind=='merge':
      keep,drop=candidate['keep'],candidate['drop'];phi=lambda z:keep if z==drop else z
      new={(s,b):(w,d,phi(z)) for(s,b),(w,d,z) in old.items() if s!=drop}
      new[keep,0],new[keep,1]=map(tuple,candidate['rows']);newstart=phi(start)
      f=shared.local_filter(old,new,domain,keep,drop,caches[seed],fuel=97,radius=7)
      result={'status':'BLANK_FILTER_SURVIVOR'} if f is None else {'status':'BOUNDARY_FILTER_REJECTED','failure':f}
     else:
      drop=candidate.get('hidden',198);entry=tuple(candidate.get('entry',[66,0]));new={row:act for row,act in old.items() if row[0]!=drop};new[entry]=tuple(candidate['action']);newstart=start
      assert [row for row,act in old.items() if act[2]==drop]==[entry]
      patterns=sorted(m for m in domain[entry[0]] if (m>>7)&1==entry[1]);cache=hiddencaches.setdefault((seed,drop),{})
      result=hidden.check_entry(old,new,drop,entry,patterns,cache,7,97,deadline)
      if result['status']=='INCOMPLETE_TIME_LIMIT':stop='TIME_LIMIT';break
     record={'family':name,'prior_id':candidate['id'],'seed':seed,'discarded_prior_window':failure['window'],'old_row':[q,bit],'result':result}
     stream.write(json.dumps(record,separators=(',',':'))+'\n')
     if result['status']=='BOUNDARY_FILTER_REJECTED':r['rejected']+=1;per['rejected']+=1
     else:
      hit=out/f'survivor-{total:06d}';hit.mkdir();native=hit/'candidate.native.tm';native.write_bytes(shared.encode(new,newstart))
      dump(hit/'candidate.json',candidate);dump(hit/'filter.json',record)
      result['scope']='Blank-seeded domain only. Independent blank-relative certificate required; no universal checker claim.'
      h={'family':name,'prior_id':candidate['id'],'seed':seed,'path':str(hit),'native_sha256':sha(native),'new_start':newstart};hits.append(h);r['survivors']+=1;per['survivors']+=1;print(json.dumps({'BLANK_FILTER_SURVIVOR':h}),flush=True)
   r['status']='COMPLETE' if r['processed']==r['candidate_count'] else 'INCOMPLETE_TIME_LIMIT'
   if stop:break
 assert all(sha(Path(p))==h for p,h in pins.items())
 output={'status':'COMPLETE_BLANK_RESCREEN' if stop is None else 'INCOMPLETE_'+stop,'seconds':time.monotonic()-started,'families':stats,'rescreened':total,'hits':hits,'inputs':pins,'source_sha256':sha(Path(__file__)),'domain_source_sha256':sha(OWN/'blank_domain.py'),'result_stream_sha256':sha(out/'rescreened.jsonl.gz'),'radius':7,'fuel':97,'limits':{'internal_seconds':115,'external_seconds':120},'scope':'Only prior rejection windows absent from the blank-seeded inductive domain are rerun. Retained windows still witness the same bounded rejection. Blank-relative discovery only, not all-initial-tape equivalence; independent verifier required for survivors.'}
 dump(out/'result.json',output);print(json.dumps({k:v for k,v in output.items() if k not in('inputs','families')},indent=2))
if __name__=='__main__':main()
