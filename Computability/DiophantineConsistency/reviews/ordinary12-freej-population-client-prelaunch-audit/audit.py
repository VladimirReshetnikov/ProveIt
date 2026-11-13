#!/usr/bin/env python3
"""No-Lean exact-byte prelaunch review, with real monitor/fake-loop controls."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-population-client-prototype';HERE=Path(__file__).resolve().parent
DRIVER=PKG/'replay.py';EXPECTED='793a6873afd3517b85828e54421ee16cbd6077091b08318fb6bc62611d20de8f'
def need(b,m):
 if not b:raise ValueError(m)
def main():
 name=DRIVER.relative_to(ROOT).as_posix();original=subprocess.run(['git','show','d27dd1f81a:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(original).hexdigest()==hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'exact driver')
 spec=importlib.util.spec_from_file_location('reviewed_driver',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 scan,parent=m.verify();need(len(scan['preferred_rebuild'])==9 and len(scan['freej_base_objects'])==97 and parent['status']=='PASS_INDEPENDENT_FREEJ_POWER_FINISH_AUDIT','real preflight')
 outputs={}
 for name,script in [('fake_loop',HERE/'mock_loop.py'),('guard_controls',HERE/'guards.py'),('monitor_controls',BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/test_monitor.py')]:
  r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],capture_output=True,text=True,timeout=120)
  need(r.returncode==0 and not r.stderr,'control '+name+' '+str((r.returncode,r.stderr)))
  outputs[name]={'exit':r.returncode,'stdout':r.stdout}
 need('good PASS fake_children 22' in outputs['fake_loop']['stdout'] and 'PASS_DENOMINATOR_MONITOR_NEGATIVE_CONTROLS' in outputs['monitor_controls']['stdout'],'control outcomes')
 need(hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'post driver drift')
 print(json.dumps({'status':'PASS_CONDITIONAL_FREEJ_POPULATION_CLIENT_PRELAUNCH_AUDIT','driver_commit':'d27dd1f81a','driver_sha256':EXPECTED,'real_preflight_preferred_sources':9,'real_preflight_base_objects_per_side':97,'real_power_parent_audit_status':parent['status'],'controls':outputs,'scope':'No Lean compile. Conditional on trusted clean initial loader environment and externally enforced stable HEAD. Frozen inputs and inherited providers are checked at points in time; no continuous integrity, package-transitive/dynamic coverage or hard process-tree quota. --deps and audit subprocesses lack monitored RSS/group bounds.'},indent=2))
if __name__=='__main__':main()
