"""Owned bounded exact six-cell scanner51 entry-action pilot."""
from pathlib import Path
import sys,json,time,collections,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'k223_merged_runtime_audit/runtime'));import independent_runtime as R
path=ROOT/'research217_bootstrap/crossover30/initialized217.native.tm';raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()=='616aaa7430ba035f130d6a8c7bc2b84197d771aba6ea26e91f89ecbd30d64fde';T=R.table(path);states=sorted({q for q,b in T});assert len(states)==217
cases=[]
# mask bit0 is physical offset-4, bit3 is offset-1.
for mask in range(16):cases.append(dict(kind='right1',mask=mask,right=1,target=1,output_right=0))
for mask in(0,5,6,7):cases.append(dict(kind='boot_right0',mask=mask,right=0,target=1,output_right=1))
for mask in(1,3,9,11):cases.append(dict(kind='decoder_right0',mask=mask,right=0,target=137,output_right=0))
start=time.monotonic();steps=0
class Cap(Exception):pass

def attempt(action,case):
 global steps
 initial={i-4:(case['mask']>>i)&1 for i in range(4)}|{0:0,1:case['right']};tape=initial.copy();want=initial.copy();want[1]=case['output_right'];w,d,q=action;tape[0]=w;h=d;trace=[[51,0,0,w,d,q]];seen=set();steps+=1
 for k in range(1,33):
  if q==case['target']and h==0 and tape==want:return dict(status='PASS',duration=k,trace=trace)
  if q==254:return dict(status='HALT_BEFORE_ENDPOINT',trace=trace)
  if q==51:return dict(status='INTERIOR51_UNSUPPORTED',trace=trace)
  if h not in tape:return dict(status='EXTERIOR_READ_UNSUPPORTED',state=q,head=h,trace=trace)
  key=q,h,tuple(tape.values())
  if key in seen:return dict(status='EXACT_PATCH_CYCLE',trace=trace)
  seen.add(key)
  if k==32:return dict(status='32_STEP_UNKNOWN',state=q,head=h,trace=trace)
  if steps>=700000 or time.monotonic()-start>=5:raise Cap('aggregate budget')
  bit=tape[h];w,d,z=T[q,bit];trace.append([q,h,bit,w,d,z]);tape[h]=w;h+=d;q=z;steps+=1

def main():
 actions=[(w,d,q)for w in(0,1)for d in(-1,1)for q in states];reports=[];hits=[];near=[];aggregate=collections.Counter()
 try:
  for action in actions:
   results=[attempt(action,case)for case in cases];counts=collections.Counter(r['status']for r in results);aggregate.update(counts);passes=[i for i,r in enumerate(results)if r['status']=='PASS'];bad=next((i for i,r in enumerate(results)if r['status']!='PASS'),None)
   rec=dict(action=action,status_counts=dict(counts),pass_case_indices=passes,first_failure=None if bad is None else dict(case_index=bad,result=results[bad]));reports.append(rec)
   if bad is None:hits.append(dict(action=action,witnesses=results))
   elif len(passes)>=16:near.append(dict(action=action,passed=len(passes),passed_kinds=dict(collections.Counter(cases[i]['kind']for i in passes)),failures=[dict(case_index=i,status=r['status'])for i,r in enumerate(results)if r['status']!='PASS']))
 except Cap as e:aggregate['AGGREGATE_CAP_UNKNOWN']+=1
 out=dict(status='COMPLETE'if len(reports)==len(actions)else'INCOMPLETE',table_sha256=hashlib.sha256(raw).hexdigest(),source_sha256='a2c2620f637905eca0126ba73fd59861ccc5e9621813dc582d7e719e44bb7c51',actions_available=len(actions),actions_completed=len(reports),cases=cases,aggregate_status_counts=dict(aggregate),matches=hits,near_matches=near,reports=reports,transitions=steps,seconds=time.monotonic()-start,scope='Entry51/read0 replacement only; all217 existing target states, two writes and two motions. Exact restoration of six-cell tape patch offsets-4..+1 except prescribed+1 update and exact target state/head, positive1..32steps, no interior halt. Exterior queries and51 revisits unsupported,32-step cutoffs unknown. Right1 universally covers all16 left4 values; right0 uses eight supplied fixed masks. No global/runtime/startup claim follows from a finite family result.')
 (OUT/'SCANNER51_FIXED_WORD_SCREEN.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in('cases','reports')},indent=2))
if __name__=='__main__':main()
