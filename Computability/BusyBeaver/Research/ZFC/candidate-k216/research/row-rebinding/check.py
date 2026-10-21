#!/usr/bin/env python3
"""Own exact 62-by-64 cylinder rebinding to K216; no imported discovery code."""
from pathlib import Path
import argparse,hashlib,json,itertools,time
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();k=(int(q),int(b));assert k not in t and b in('0','1')and w in('0','1')and d in('L','R');t[k]=(int(w),1 if d=='R'else-1,int(z))
 qs={q for q,b in t};assert set(t)=={(q,b)for q in qs for b in(0,1)};assert{z for w,d,z in t.values()}-qs=={254};return t,qs

def check(T,row,replacement):
 answer=[];failures=[]
 for bits in itertools.product((0,1),repeat=6):
  window=list(bits[:3])+[row[1]]+list(bits[3:]);old=list(window);w,d,z=T[row];old[3]=w;expected=(z,3+d,old)
  q=row[0];h=3;tape=list(window);path=[];success=False
  for n in range(1,4):
   if not 0<=h<7:reason='outside window before reading';break
   key=(q,tape[h])
   if key not in T:reason='halt before matching';break
   action=replacement if key==row else T[key]
   path.append([q,h,tape[h],*action]);tape[h],d,q=action;h+=d
   if (q,h,tape)==expected:success=True;answer.append({'window':window,'steps':n,'path':path});break
  if not success:failures.append({'window':window,'path':path,'end':[q,h,tape],'expected':[expected[0],expected[1],expected[2]],'reason':reason if len(path)<3 else 'not joined in three steps'})
 return answer,failures

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True);ap.add_argument('--variants',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir(parents=True,exist_ok=False);start=time.monotonic()
 assert sha(a.table)=='2efb7adf9cfcbea58197a2bde2610b22f58b647f05385bc716b036242be6fa6c'
 assert sha(a.variants)=='8bdddabff28e56575d921808d738fab2ce9d6604434692b6a552cb834b789826'
 T,qs=read(a.table);assert len(qs)==216
 records=[]
 for i,line in enumerate(a.variants.read_text().splitlines()):
  q,b,w,d,z,n=line.split();row=(int(q),int(b));action=(int(w),1 if d=='R'else-1,int(z));assert row in T and action[2]in qs and int(n)==3
  cases,fail=check(T,row,action);assert len(cases)+len(fail)==64
  rec={'index':i,'row':row,'old':T[row],'replacement':action,'status':'ALL_TAPES_ONE_ROW_REFINEMENT'if not fail else'BOUNDED_DIAGRAM_NOT_ESTABLISHED','passed_cylinders':len(cases),'failed_cylinders':len(fail),'diagrams':cases,'failures':fail}
  if not fail:
   N=dict(T);N[row]=action;reachable={0};todo=[0]
   while todo:
    q=todo.pop()
    for b in(0,1):
     z=N[q,b][2]
     if z!=254 and z not in reachable:reachable.add(z);todo.append(z)
   rec['graph_reachable_working_states']=len(reachable)
  records.append(rec)
 assert len(records)==62
 # An immediate false halt cannot match this nonhalting old one-step boundary.
 good,bad=check(T,(0,0),(0,1,254));assert not good and len(bad)==64
 result={'status':'EXACT_REBINDING_COMPLETE','table':str(a.table.resolve()),'table_sha256':sha(a.table),'variants':str(a.variants.resolve()),'variants_sha256':sha(a.variants),'checker_sha256':sha(Path(__file__)),'tested_variants':len(records),'cylinders':64*len(records),'passed_variants':[x['index']for x in records if not x['failures']],'failed_variants':[x['index']for x in records if x['failures']],'negative_control_rejected_cylinders':len(bad),'seconds':time.monotonic()-start,'scope':'Each passed rewrite separately preserves every original one-step boundary on every tape by a positive at-most-three-step path reading only its complete seven-cell cylinder. Outside tape arbitrary and untouched. This proves halting equivalence by block composition, not new minimum-state/runtime evidence. Failed diagrams are only failures of this fixed local criterion. No simultaneous composition is certified.','records':records}
 (a.output/'result.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
 print(json.dumps({k:v for k,v in result.items()if k!='records'},indent=2))
if __name__=='__main__':main()
