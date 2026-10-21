"""Owned two specific cooperative scanner families, exact six-cell endpoints."""
from pathlib import Path
import sys,json,time,collections,hashlib
ROOT=Path(__file__).resolve().parents[1];OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'k223_merged_runtime_audit/runtime'));import independent_runtime as R
sys.path.insert(0,str(ROOT/'research218_encoding'));import mixed_detours as M
path=ROOT/'research217_bootstrap/crossover30/initialized217.native.tm';raw=path.read_bytes();assert hashlib.sha256(raw).hexdigest()=='616aaa7430ba035f130d6a8c7bc2b84197d771aba6ea26e91f89ecbd30d64fde';T=R.table(path);states=sorted({q for q,b in T});assert len(states)==217
cases=[dict(kind='boot',mask=m,target=1,output_right=1)for m in(0,5,6,7)]+[dict(kind='decoder',mask=m,target=137,output_right=0)for m in(1,3,9,11)]
start=time.monotonic();steps=0
class Cap(Exception):pass

def trial(U,case):
 global steps
 initial={i-4:(case['mask']>>i)&1 for i in range(4)}|{0:0,1:0};tape=initial.copy();want=initial.copy();want[1]=case['output_right'];q=51;h=0;seen=set();trace=[]
 for k in range(65):
  if k and q==case['target']and h==0 and tape==want:return dict(status='PASS',duration=k,trace=trace)
  if q==254:return dict(status='HALT_BEFORE_ENDPOINT',trace=trace)
  if k and q==51:return dict(status='INTERIOR51_UNSUPPORTED',trace=trace)
  if h not in tape:return dict(status='EXTERIOR_READ_UNSUPPORTED',state=q,head=h,trace=trace)
  key=q,h,tuple(tape.values())
  if key in seen:return dict(status='EXACT_PATCH_CYCLE',trace=trace)
  seen.add(key)
  if k==64:return dict(status='64_STEP_UNKNOWN',state=q,head=h,trace=trace)
  if steps>=1000000 or time.monotonic()-start>=5:raise Cap('aggregate budget')
  b=tape[h];w,d,z=U[q,b];trace.append([q,h,b,w,d,z]);tape[h]=w;h+=d;q=z;steps+=1

def main():
 reports=[];hits=[];near=[];aggregate=collections.Counter()
 try:
  for keeper in(16,122):
   # Uniform proof of the right1 branch:51/0 preserves0 and advances to
   # keeper; keeper/1 clears that1 and returns1 at the original head.
   assert T[keeper,1]==(0,-1,1)
   for w in(0,1):
    for d in(-1,1):
     for q in states:
      action=(w,d,q);U=T.copy();U[51,0]=(0,1,keeper);U[keeper,0]=action
      results=[trial(U,case)for case in cases];counts=collections.Counter(x['status']for x in results);aggregate.update(counts);passed=[i for i,r in enumerate(results)if r['status']=='PASS'];bad=next((i for i,r in enumerate(results)if r['status']!='PASS'),None)
      rec=dict(keeper=keeper,action=action,status_counts=dict(counts),pass_case_indices=passed,first_failure=None if bad is None else dict(case_index=bad,result=results[bad]));reports.append(rec)
      if bad is None:
       dest=OUT/f'scanner51_hit_{keeper}_{w}_{d}_{q}';dest.mkdir(exist_ok=True);bytes_=M.enc(U);(dest/'candidate217.native.tm').write_bytes(bytes_);hit=dict(keeper=keeper,action=action,witnesses=results,table_sha256=hashlib.sha256(bytes_).hexdigest(),directory=str(dest.relative_to(ROOT)));hits.append(hit)
      elif len(passed)>=4:near.append(dict(keeper=keeper,action=action,passed=len(passed),passed_kinds=dict(collections.Counter(cases[i]['kind']for i in passed)),failures=[dict(case_index=i,status=r['status'])for i,r in enumerate(results)if r['status']!='PASS']))
 except Cap:aggregate['AGGREGATE_CAP_UNKNOWN']+=1
 out=dict(status='COMPLETE'if len(reports)==1736 else 'INCOMPLETE',table_sha256=hashlib.sha256(raw).hexdigest(),source_sha256='a2c2620f637905eca0126ba73fd59861ccc5e9621813dc582d7e719e44bb7c51',architectures=['51/0=0R16, vary16/0','51/0=0R122, vary122/0'],choices_available=1736,choices_completed=len(reports),right1_generic_trace='51/0=0Rkeeper;keeper/1=0L1, exact2steps for every exterior tape',cases=cases,aggregate_status_counts=dict(aggregate),matches=hits,near_matches=near,reports=reports,transitions=steps,seconds=time.monotonic()-start,scope='Only these two cooperative entry architectures. Exact six-cell tape/state/head endpoint, at most64steps, no halt crossed. Keeper revisits use the actual patched row.51revisits/exterior queries unsupported; fuel cutoff unknown. Other existing16/122 arithmetic/source roles, fullruntime and blank initialization NOT certified by a local match.')
 (OUT/'SCANNER51_TWO_STAGE_SCREEN.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in('cases','reports')},indent=2))
if __name__=='__main__':main()
