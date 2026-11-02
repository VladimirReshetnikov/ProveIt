#!/usr/bin/env python3
"""No-Lean exact-byte source and mocked-control review; no full parent replay."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';HERE=Path(__file__).resolve().parent
DRIVER=BASE/'research/ordinary12-ipra-bridge/compact44-relabel-pair-prototype/replay.py';EXPECTED='f2d574483b92a6648462a2700a23e2884ea5572c8f5b2162ccf6b068c9d61510'
def need(b,m):
 if not b:raise ValueError(m)
def main():
 name=DRIVER.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','d1b4a61bb4:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(blob).hexdigest()==hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'driver pin')
 spec=importlib.util.spec_from_file_location('relabel_review',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 m.check_pins();need(len(m.NAMES)==58 and len(set(m.NAMES))==58,'manifest count')
 result={}
 for name in ('mock_loop.py','guards.py'):
  r=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/name)],cwd=ROOT,capture_output=True,text=True,timeout=120)
  need(r.returncode==0 and not r.stderr,'control '+name+' '+r.stderr);result[name]={'exit':r.returncode,'stdout':r.stdout}
 need('good PASS fake_children 116' in result['mock_loop.py']['stdout'],'full loop')
 need(hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'post driver drift')
 print(json.dumps({'status':'PASS_CONDITIONAL_COMPACT44_RELABEL_PRELAUNCH_AUDIT','driver_commit':'d1b4a61bb4','driver_sha256':EXPECTED,'manifest_sha256':m.MANIFEST_SHA,'source_anchor_checks':58,'preflight_recorded_head':'d1b4a61bb4d2e37620855f929fb451ca0aa485ec','recorded_preflight_session':35056,'recorded_preflight_exit':0,'controls':result,'scope':'No Lean build. Original full preflight was separately observed; this script reruns source/anchor and mocked controls, not full parent preflight. Clean initial loader and externally stable HEAD/sole-Lean window required; provider/source checks are point-in-time and sampled monitors are not quotas.'},indent=2))
if __name__=='__main__':main()
