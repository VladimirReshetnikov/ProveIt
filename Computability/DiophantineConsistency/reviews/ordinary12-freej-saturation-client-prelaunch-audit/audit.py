#!/usr/bin/env python3
"""Conditional no-Lean prelaunch audit of the saturation paired wrapper."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';HERE=Path(__file__).resolve().parent
PKG=BASE/'research/ordinary12-ipra-bridge/free-j-saturation-client-prototype';DRIVER=PKG/'replay.py';EXPECTED='05e5563e0eaf17f7beb6a6e0b5412159b488c12fa615806d85b8678cef917d3f'
def need(b,m):
 if not b:raise ValueError(m)
def main():
 name=DRIVER.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','37d04291e8:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(blob).hexdigest()==hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'driver bytes')
 spec=importlib.util.spec_from_file_location('saturation_review',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 scan,parent=m.verify();need(len(scan['modules'])==4 and len(scan['inherited_objects'])==109 and parent['status']=='PASS_INDEPENDENT_FREEJ_POPULATION_CLIENT_AUDIT','real preflight')
 checks=[]
 for script,args,expected in [(HERE/'mock_loop.py',[],0),(HERE/'guards.py',[],0),(PKG/'warning_policy.py',[],0),(PKG/'warning_policy.py',['-O'],1),(BASE/'research/ordinary12-ipra-bridge/free-j-current-denominator-composition/test_monitor.py',[],0)]:
  r=subprocess.run([sys.executable,*args,'-I','-S','-B',str(script)],capture_output=True,text=True,timeout=120)
  need((r.returncode==0 if expected==0 else r.returncode!=0),'control exit '+str(script))
  if expected:need('optimized Python rejected' in r.stderr,'optimized guard')
  else:need(not r.stderr,'control stderr '+str(script))
  checks.append({'script':script.name,'args':args,'exit':r.returncode,'stdout':r.stdout})
 need('good PASS fake_children 10' in checks[0]['stdout'] and 'PASS_DENOMINATOR_MONITOR_NEGATIVE_CONTROLS' in checks[-1]['stdout'],'control output')
 need(hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'post driver pin')
 print(json.dumps({'status':'PASS_CONDITIONAL_FREEJ_SATURATION_PRELAUNCH_AUDIT','driver_commit':'37d04291e8','driver_sha256':EXPECTED,'real_preflight_source_count':4,'inherited_objects_per_side':109,'parent_audit_status':parent['status'],'controls':checks,'scope':'No Lean compilation; exact four linter warnings accepted, no graph premise discharge. Requires clean initial loader and externally protected stable HEAD/sole-Lean window. Point-in-time source/provider checks, unmonitored deps/audits and sampled-resource limits remain.'},indent=2))
if __name__=='__main__':main()
