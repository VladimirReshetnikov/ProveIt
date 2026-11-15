#!/usr/bin/env python3
"""Fresh literal blank-start diagnosis of every recognized 193-control graph.

For each possible working start, check a finite halt, exact repeated configuration,
or a self-loop moving out into a genuinely blank half-line. A ray certificate is
an exact infinite nonhalting proof, not extrapolation from a simulation. The
attempted loop-reassociation graph is separately documented as source-invalid;
resource-limit outcomes remain unresolved by this diagnostic.
"""
import argparse,collections,hashlib,importlib.util,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent
sp=importlib.util.spec_from_file_location('audit',HERE/'audit_corpus.py');au=importlib.util.module_from_spec(sp);sp.loader.exec_module(au)

def run(data,start,limit,store_trace=False):
 rows,states,halt=data;q=start;h=0;ones=set();seen={};trace=[]
 for t in range(limit+1):
  if q==halt:return {'status':'HALT','steps':t,'state':q,'head':h,'ones':sorted(ones),'trace':trace if store_trace else None}
  if t==limit:return {'status':'LIMIT','steps':t,'state':q,'head':h,'ones':sorted(ones),'trace':trace if store_trace else None}
  b=int(h in ones);w,d,n=rows[q,b];direction=1 if d=='R' else -1
  if b==0 and n==q and (not ones or (h>max(ones) if direction>0 else h<min(ones))):
   return {'status':'RAY','steps':t,'state':q,'head':h,'ones':sorted(ones),'ray_action':[w,d,n],'blank_half_line':'right' if direction>0 else 'left','trace':trace if store_trace else None}
  # Exact repeats; avoid retaining huge configurations for the rejected loop table.
  if len(ones)<200:
   key=(q,h,tuple(sorted(ones)))
   if key in seen:return {'status':'CYCLE','steps':t,'entry_steps':seen[key],'state':q,'head':h,'ones':sorted(ones),'trace':trace if store_trace else None}
   seen[key]=t
  if store_trace:trace.append([q,h,b,w,d,n])
  if w:ones.add(h)
  else:ones.discard(h)
  q=n;h+=direction
 raise AssertionError

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--census',type=pathlib.Path,required=True);ap.add_argument('--output',type=pathlib.Path,required=True);ap.add_argument('--limit',type=int,default=100000);a=ap.parse_args();j=json.loads(a.census.read_text());results=[]
 for i,c in enumerate(x for x in j['classes'] if x['states']==193):
  raw=(a.census.parent/'representatives'/(c['action_graph_sha256']+'.tm')).read_bytes();data=au.parse_text(raw);assert data
  badloop='pa194_loop_continuation' in c['representative']['path']
  # Separate prospective start from table-only equivalence. Source packets use native74,
  # except the dense rejected candidate with start0. Every possible start is diagnosed.
  starts=sorted(data[1]);out=[]
  for s in starts:
   rr=run(data,s,a.limit);rr.pop('ones',None);rr.pop('trace',None);out.append({'start':s,**rr})
  natural=c['representative']['designated_start']
  if natural is None:natural=74 if 74 in data[1] else None
  natural_run=run(data,natural,a.limit,True) if natural is not None and not badloop else None
  rr={'action_graph_sha256':c['action_graph_sha256'],'representative_source':c['representative']['path'],'normalized_sha256':au.sha(au.normalized(data)),'working_states':193,'all_start_outcomes':out,'counts':dict(collections.Counter(x['status'] for x in out)),'intended_start':natural,'intended_start_basis':'dense table convention' if c['representative']['designated_start'] is not None else 'native74 protocol as documented by source packets; all possible starts tested separately','intended_run':natural_run,'source_invalid_loop':badloop}
  results.append(rr);print(i,rr['action_graph_sha256'][:12],rr['counts'],flush=True)
 total=collections.Counter(x['status'] for r in results for x in r['all_start_outcomes'])
 summary={'classes':len(results),'all_possible_start_cases':sum(len(x['all_start_outcomes']) for x in results),'outcomes':dict(total),'classes_every_start_resolved':sum(not r['counts'].get('LIMIT',0) for r in results),'classes_with_limits':[r['action_graph_sha256'] for r in results if r['counts'].get('LIMIT',0)],'intended_start_counts':dict(collections.Counter(r['intended_run']['status'] for r in results if r['intended_run'])),'scope':__doc__}
 a.output.write_text(json.dumps({'summary':summary,'tables':results},indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
