#!/usr/bin/env python3
"""Read-only audit of the finished live Rocq build; invokes no compiler."""
from pathlib import Path
import argparse,hashlib,json,time

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--build',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();r=a.build.resolve()
 plan=json.loads((r/'plan.json').read_text());tc=json.loads((r/'toolchain.json').read_text())
 assert plan['target']=='K215F.CorrectDense215' and plan['count']==237 and plan['reference_count']==195
 assert len(plan['order'])==len(set(plan['order']))==237 and plan['order'][-1]==plan['target']
 assert set(plan['modules'])==set(plan['order'])
 closure=set()
 def visit(n):
  if n in closure:return
  closure.add(n)
  for d in plan['modules'][n]['dependencies']:visit(d)
 visit(plan['target']);assert closure==set(plan['order'])
 assert 'version 9.1.0' in tc['compiler'] and tc['stdlib']=='9.0.0'
 reports={};records={};objects={};seconds=0
 for n in plan['order']:
  m=plan['modules'][n];recpath=r/'records'/(n+'.json');rec=json.loads(recpath.read_text())
  assert rec['module']==n and rec['status']=='PASS' and rec['exit_code']==0 and rec['post_inputs_unchanged'] is True,n
  src=Path(m['source']);obj=Path(m['target']).with_suffix('.vo');snap=Path(rec['source_snapshot']);log=snap.parent/'output.log'
  assert sha(src)==sha(snap)==rec['source_sha256'],n
  assert sha(log)==rec['output_sha256'] and sha(obj)==rec['object_sha256'],n
  expected={str(src):sha(src)}
  for dep in m['dependencies']:
   target=Path(plan['modules'][dep]['target']).with_suffix('.vo');expected[str(target)]=sha(target)
  assert rec['inputs']==expected,n
  if 'expected_reference_sha256' in m:assert rec['source_sha256']==m['expected_reference_sha256'],n
  text=log.read_text()
  if n in ('K215F.Correct215','K215F.CorrectDense215'):
   assert text.count('Closed under the global context')==2 and 'Axioms:' not in text,n
   reports[n]={'closed_reports':2,'raw_log':str(log),'raw_log_sha256':sha(log)}
  records[n]=sha(recpath);objects[str(obj)]=sha(obj);seconds+=rec['seconds']
  compiler=Path(rec['argv'][0]);assert sha(compiler)==tc['coqc_sha256']
  opts=['-w','-deprecated,-notation-overridden']
  if n.startswith('Undecidability.'):opts+=['-set','Default Proof Using = Type']
  assert rec['argv']==[str(compiler),*plan['flags'],*opts,m['target']],n
 assert len(reports)==2
 kernels=sorted((r/'kernel').glob('run*/record.json'),key=lambda p:int(p.parent.name[3:]));assert kernels
 kp=kernels[-1];k=json.loads(kp.read_text());log=kp.parent/'output.log'
 assert k['status']=='PASS' and k['exit_code']==0 and k['post_inputs_unchanged'] is True
 assert k['inputs']==objects and sha(log)==k['output_sha256']
 checker=Path(k['argv'][0]);assert sha(checker)==tc['coqchk_sha256']
 assert k['argv']==[str(checker),*plan['flags'],'-silent','-o','K215F.CorrectDense215']
 result={'status':'PASS_CLOSED_KERNEL','reviewed_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'scope':'Read-only live-source/object/log audit; no compiler invocation or inferred replay.','target':plan['target'],'compiled_modules':237,'pinned_reference_modules':195,'K215_modules':42,'plan_sha256':sha(r/'plan.json'),'toolchain':tc,'toolchain_record_sha256':sha(r/'toolchain.json'),'module_record_sha256':records,'endpoint_assumptions':reports,'kernel_record':str(kp),'kernel_record_sha256':sha(kp),'kernel_log_sha256':sha(log),'source_compile_seconds':seconds,'kernel_seconds':k['seconds'],'all_current_source_snapshot_dependency_object_bindings_match':True,'actual_vs_portable':'Actual compiler runner is retained separately. Its final raw endpoint reports are checked here independently of cache eligibility metadata.'}
 a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ('status','compiled_modules','source_compile_seconds','kernel_seconds')},indent=2))
if __name__=='__main__':main()
