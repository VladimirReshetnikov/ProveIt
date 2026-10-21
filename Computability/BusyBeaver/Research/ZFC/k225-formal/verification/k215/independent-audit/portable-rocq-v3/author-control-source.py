#!/usr/bin/env python3
"""No proof compilers: regression controls for saved-record gates and child cleanup."""
from pathlib import Path
import importlib.util,hashlib,json,os,signal,subprocess,sys,tempfile,time
ROOT=Path('/tmp/k215-rocq-complete')
DRIVER=Path('/home/codex/.codex/worktrees/ec20/Proofs/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/rocq/build.py')
spec=importlib.util.spec_from_file_location('portable',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
checks={}
with tempfile.TemporaryDirectory(prefix='k215-runner-controls-') as td:
 p=Path(td);obj=p/'test.vo';obj.write_bytes(b'fake object, no Rocq invocation\n');log=p/'output.log';snapshot=p/'Test.v';snapshot.write_text('fake source\n')
 output='Closed under the global context\nClosed under the global context\n';log.write_text(output)
 old={'module':'K215F.CorrectDense215','status':'PASS','exit_code':0,'post_inputs_unchanged':True,'inputs':{'a':'b'},'object_sha256':m.sha(obj),'source_snapshot':str(snapshot),'output_sha256':m.sha(log)}
 checks['valid_endpoint_reusable']=m.reusable(old,{'a':'b'},obj)
 log.write_text(output+'Axioms:\nbad : False\n');bad=dict(old,output_sha256=m.sha(log))
 checks['axiom_endpoint_rejected']=not m.reusable(bad,{'a':'b'},obj)
 log.write_text('Closed under the global context\n');bad=dict(old,output_sha256=m.sha(log))
 checks['missing_closed_report_rejected']=not m.reusable(bad,{'a':'b'},obj)
 log.write_text(output);bad=dict(old,output_sha256='0'*64)
 checks['changed_saved_log_rejected']=not m.reusable(bad,{'a':'b'},obj)
 checks['failed_gate_record_rejected']=not m.reusable(dict(old,status='FAIL_ASSUMPTIONS'),{'a':'b'},obj)
 tc=p/'toolchain.json';m.bind_toolchain(tc,{'compiler':'one','stdlib':'same'});before=tc.read_bytes()
 m.bind_toolchain(tc,{'compiler':'one','stdlib':'same'});checks['same_toolchain_accepted']=tc.read_bytes()==before
 try:m.bind_toolchain(tc,{'compiler':'two','stdlib':'same'})
 except AssertionError:checks['changed_toolchain_rejected_without_overwrite']=tc.read_bytes()==before
 else:checks['changed_toolchain_rejected_without_overwrite']=False
 child=p/'child.py';child.write_text('import subprocess,sys,os,time,json\nfrom pathlib import Path\ng=subprocess.Popen([sys.executable,"-c","import time; time.sleep(60)"])\nPath(sys.argv[1]).write_text(json.dumps([os.getpid(),g.pid]))\ntime.sleep(60)\n')
 control=p/'controller.py';control.write_text('import importlib.util,sys,signal,os\nfrom pathlib import Path\ns=importlib.util.spec_from_file_location("driver",sys.argv[1]);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)\nsignal.signal(signal.SIGTERM,m.stop_signal)\nwith open(sys.argv[3],"w") as log:m.proof_process([sys.executable,sys.argv[2],sys.argv[4]],os.environ,Path(sys.argv[2]).parent,log)\n')
 ids=p/'pids.json';raw=p/'controller.log';t=time.monotonic()
 with raw.open('w') as out:
  proc=subprocess.Popen([sys.executable,str(control),str(DRIVER),str(child),str(p/'child.log'),str(ids)],stdout=out,stderr=subprocess.STDOUT)
  while not ids.exists() and time.monotonic()-t<5:time.sleep(.01)
  assert ids.exists(),'fake child did not start'
  child_ids=json.loads(ids.read_text());proc.send_signal(signal.SIGTERM)
  try:rc=proc.wait(timeout=15)
  except subprocess.TimeoutExpired:
   os.killpg(child_ids[0],signal.SIGKILL);proc.kill();proc.wait();raise
 def live(pid):
  try:return Path('/proc/'+str(pid)+'/stat').read_text().split()[2]!='Z'
  except FileNotFoundError:return False
 checks['sigterm_reaps_child_and_stops_group']=rc!=0 and all(not live(pid) for pid in child_ids)
 (ROOT/'portable-sigterm-control.log').write_bytes(raw.read_bytes())
 result={'status':'PASS' if all(checks.values()) else 'FAIL','checks':checks,'driver_sha256':m.sha(DRIVER),'scope':'Fake source/object/log fixtures and disposable Python child/grandchild only; no Rocq or Lean compiler invoked.','sigterm_seconds':time.monotonic()-t}
 (ROOT/'portable-controls.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));assert all(checks.values())
