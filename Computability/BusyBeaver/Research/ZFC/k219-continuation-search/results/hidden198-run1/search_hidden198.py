#!/usr/bin/env python3
"""Delete unique-entry state198 by a positive macro from66/0, not a quotient.
Survivors require a separate independent boundary-macro verifier before use.
"""
from pathlib import Path
import argparse,collections,gzip,hashlib,itertools,json,sys,time
import search_v3 as shared
P=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def check_entry(old,new,patterns,radius=7,fuel=97):
 histogram=collections.Counter()
 for word in patterns:
  oldq,oldh,oldm=66,0,word;goals={};oldhalt=None
  for n in range(1,fuel+1):
   if oldq==254 or not -radius<=oldh<=radius:break
   bit=(oldm>>(oldh+radius))&1;w,d,oldq=old[oldq,bit]
   oldm=(oldm&~(1<<(oldh+radius)))|(w<<(oldh+radius));oldh+=d
   if oldq==254:oldhalt=n
   if oldq!=198:goals.setdefault((oldq,oldh,oldm),n)
  q,h,m=66,0,word;seen=set();joined=None;reason='fuel_exhausted'
  for tick in range(1,fuel+1):
   if q==254 or not -radius<=h<=radius:reason='new_exits_window';break
   if (q,h,m) in seen:reason='new_repeats';break
   seen.add((q,h,m));bit=(m>>(h+radius))&1;w,d,q=new[q,bit]
   m=(m&~(1<<(h+radius)))|(w<<(h+radius));h+=d
   if q==254:
    if oldhalt is not None:joined=(oldhalt,tick)
    else:reason='new_halt_without_old_halt'
    break
   n=goals.get((q,h,m))
   if n is not None:joined=(n,tick);break
  if joined is None:return {'status':'BOUNDARY_FILTER_REJECTED','window':word,'radius':radius,'fuel':fuel,'reason':reason}
  histogram[joined]+=1
 return {'status':'BOUNDARY_MACRO_FILTER_SURVIVOR','contexts':len(patterns),'histogram':[[a,b,n] for(a,b),n in sorted(histogram.items())],'scope':'Author boundary filter only; independent verifier required.'}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 if not __debug__ or sys.flags.optimize:ap.error('Assertions required')
 a.output.mkdir(parents=True,exist_ok=False);inputs=json.loads((P/'inputs.json').read_text());ds=inputs['seeds']+[inputs['universal_checker']]
 pins={str((P/d['path']).resolve()):d['sha256'] for d in ds};assert all(sha(Path(p))==h for p,h in pins.items())
 checker=shared.load_checker((P/inputs['universal_checker']['path']).resolve());(a.output/'search_hidden198.py').write_bytes(Path(__file__).read_bytes())
 started=time.monotonic();allstats=[];hits=[];total=0;stop=None
 with gzip.open(a.output/'rejections.jsonl.gz','wt') as rejected:
  for sd in inputs['seeds']:
   old,start=checker.read((P/sd['path']).resolve());assert start!=198 and len(old)==438
   assert [row for row,action in old.items() if action[2]==198]==[(66,0)]
   invariant=checker.domain(old,start,7);patterns=sorted(m for m in invariant[66] if ((m>>7)&1)==0)
   assert patterns and all((m>>6)&1==0 and (m>>5)&1==1 for m in patterns)
   new={row:action for row,action in old.items() if row[0]!=198};targets=sorted({q for q,b in new}|{254});assert len(targets)==219
   stats={'seed':sd['name'],'attempted':0,'rejected':0,'survivors':0,'entry_contexts':len(patterns)}
   for action in itertools.product((0,1),(-1,1),targets):
    if time.monotonic()-started>=120:stop='TIME_LIMIT';break
    new[66,0]=action;assert all(z!=198 for w,d,z in new.values())
    assert all(new[row]==value for row,value in old.items() if row[0]!=198 and row!=(66,0))
    total+=1;stats['attempted']+=1;result=check_entry(old,new,patterns)
    if result['status']=='BOUNDARY_FILTER_REJECTED':
     stats['rejected']+=1;rejected.write(json.dumps({'id':total,'seed':sd['name'],'action':list(action),'failure':result},separators=(',',':'))+'\n')
    else:
     d=a.output/f'survivor-{total:04d}';d.mkdir();native=d/'candidate.native.tm';native.write_bytes(shared.encode(new,start));dump(d/'filter.json',result)
     hits.append({'id':total,'seed':sd['name'],'action':list(action),'candidate_sha256':sha(native),'filter':str(d/'filter.json')});stats['survivors']+=1
   allstats.append(stats)
   if stop:break
 assert all(sha(Path(p))==h for p,h in pins.items())
 out={'status':'COMPLETE_HIDDEN_CHECKPOINT_SEARCH' if stop is None else 'INCOMPLETE_'+stop,'seconds':time.monotonic()-started,'source_sha256':sha(Path(__file__)),'inputs':pins,'seeds':allstats,'attempted':total,'hits':hits,'family':'Delete198; changeonly66/0 over bothwrites,bothdirections,all218remainingstates+halt. Nootherrowchange and no state quotient.','boundary_relation':'Exact state/head/tape equality only at old states other than198; changed entry66/0 must have positive old/new blocks to such a common boundary or bothhalt.','radius':7,'fuel':97,'wall_limit':120,'candidate_limit':1752,'rejection_stream_sha256':sha(a.output/'rejections.jsonl.gz'),'scope':'No independent verifier invoked. Surviving entries would require separate verification; failures are bounded-diagram failures only, no lowerbound.'}
 dump(a.output/'result.json',out);print(json.dumps(out,indent=2))
if __name__=='__main__':main()
