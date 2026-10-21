#!/usr/bin/env python3
"""Delete CM215 helper176, synthesize52/0 and211/0 jointly.
Old helper176 is excluded from simulation cutpoints; positive old/new join
blocks must end in an identical retained state, head, and full window.
"""
from pathlib import Path
import argparse,collections,hashlib,importlib.util,itertools,json,time
p=argparse.ArgumentParser();p.add_argument('--checker',type=Path,required=True);p.add_argument('--table',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--radius',type=int,default=7);a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
s=importlib.util.spec_from_file_location('joint_checker',a.checker);b=importlib.util.module_from_spec(s);s.loader.exec_module(b);T,start=b.read(a.table);Q=sorted({q for q,_ in T});I=b.domain(T,start,a.radius);drop=176;helper=211;R=sorted(set(Q)-{drop});actions=list(itertools.product((0,1),(-1,1),R+[254]));fuel=97
assert [(q,c)for(q,c),(w,d,z)in T.items()if z==176]==[(52,0)]
patterns={q:sorted(m for m in I[q]if((m>>a.radius)&1)==0)for q in(52,helper)}
for q,ps in patterns.items():
 if len(ps)>2:patterns[q]=[ps[0],ps[-1],*ps[1:-1]]
paths={}
def goals(q,m):
 if(q,m)in paths:return paths[q,m]
 sq,sh,sm=q,0,m;g=set();halt=False
 for tick in range(1,fuel+1):
  if sq==254 or not -a.radius<=sh<=a.radius:break
  ob=(sm>>(sh+a.radius))&1;w,d,sq=T[sq,ob];sm=(sm&~(1<<(sh+a.radius)))|(w<<(sh+a.radius));sh+=d
  if sq==254:halt=True
  if sq!=176:g.add((sq,sh,sm))
 paths[q,m]=(g,halt);return g,halt
N={k:v for k,v in T.items()if k[0]!=176}
def rowcheck(q,unknown52=False):
 for m in patterns[q]:
  gs,old_halt=goals(q,m);sq,sh,sm=q,0,m;seen=set()
  for k in range(1,fuel+1):
   if sq==176:return 'removed_state'
   if sq==254:return 'unexpected_halt'
   if not -a.radius<=sh<=a.radius:return 'window_exit'
   ob=(sm>>(sh+a.radius))&1
   if unknown52 and sq==52 and ob==0:break
   state=(sq,sh,sm)
   if state in seen:return 'repeated'
   seen.add(state);w,d,sq=N[sq,ob];sm=(sm&~(1<<(sh+a.radius)))|(w<<(sh+a.radius));sh+=d
   if sq==254:
    if old_halt:break
    return 'new_halt'
   if(sq,sh,sm)in gs:break
  else:return 'fuel'
 return 'PASS'
now=time.monotonic();ys=[];filter_counts=collections.Counter()
for y in actions:
 N[helper,0]=y;out=rowcheck(helper,True);filter_counts[out]+=1
 if out=='PASS':ys.append(y)
print('provider_actions',len(ys),flush=True);tried=0;results=collections.Counter();hits=[]
for y in ys:
 N[helper,0]=y
 for x in actions:
  tried+=1;N[52,0]=x;out=rowcheck(52)
  if out=='PASS':out=rowcheck(helper)
  results[out]+=1
  if out=='PASS':
   name=f'candidate-{len(hits)}.tm';raw=(f'#! start {start}\n'+''.join(f'{q} {c} {w} {"R"if d==1 else"L"} {z}\n'for(q,c),(w,d,z)in sorted(N.items()))).encode();(a.output/name).write_bytes(raw)
   hits.append({'52/0':x,'211/0':y,'file':name,'sha256':hashlib.sha256(raw).hexdigest()});print('HIT',hits[-1],flush=True)
result={'status':'COMPLETE_BOUNDED_CUTPOINT_TWO_ROW_SEARCH','table_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(a.checker.read_bytes()).hexdigest(),'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'drop':176,'other_rewritten_row':[211,0],'radius':a.radius,'fuel':fuel,'invariant_contexts':sum(map(len,I.values())),'zero_context_counts':{str(q):len(v)for q,v in patterns.items()},'provider_rows_tried':len(actions),'provider_filter_counts':dict(filter_counts),'surviving_provider_actions':ys,'row_pairs_tried':tried,'pair_outcomes':dict(results),'hits':hits,'seconds':time.monotonic()-now,'scope':'Both52/0 and211/0 arbitrary remaining-state-or-halt actions. Prior provider filter permits unknown52/0 reentry; all hits must satisfy full local joins for both changed rows, at retained cutpoints. Window/fuel bounds incomplete.'}
(a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
