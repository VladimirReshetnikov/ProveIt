#!/usr/bin/env python3
"""No-Lean exact source and six-step mocked-control review."""
import hashlib,importlib.util,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Computability/DiophantineConsistency';HERE=Path(__file__).resolve().parent
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-low-population-exact-prototype';DRIVER=PKG/'replay.py';EXPECTED='ff72d79a6e1a2cec2074f94d5f668048bbe3690e152dc3a86eb3bd78d65edf88'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise ValueError(m)
def main():
 name=DRIVER.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','7beb48d390:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(blob).hexdigest()==sha(DRIVER)==EXPECTED,'exact driver')
 spec=importlib.util.spec_from_file_location('reviewed_low',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 for p,h in m.PINS.items():need(sha(p)==h,'fixed source/parent pin '+str(p))
 check=json.loads((m.AUDIT/'CHECK.json').read_bytes());meta=json.loads((m.PARENT/'evidence/receipt.json').read_bytes())
 need(check['status']=='PASS_INDEPENDENT_COMPACT44_CONCRETE_MASK_AUDIT' and check['recorded_outer_exit']==0 and check['receipt_sha256']==m.PINS[m.PARENT/'evidence/receipt.json'] and meta['status']=='PASS_PAIRED_COMPACT_CONCRETE_MASK' and len(meta['runs'])==2,'parent metadata')
 for row in meta['runs']:need(row['compiler_exit']==row['deps_exit']==0 and sha(m.PREFIX/row['label']/'CompactConcreteMask.olean')==row['object_sha256'],'same-side seed')
 results={}
 for script in ('mock_loop.py','guards.py'):
  r=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/script)],capture_output=True,text=True,timeout=120)
  need(r.returncode==0 and not r.stderr,'control '+script+' '+r.stderr);results[script]={'exit':r.returncode,'stdout':r.stdout}
 need('good PASS fake_children 6' in results['mock_loop.py']['stdout'],'six fake children')
 need(sha(DRIVER)==EXPECTED,'post driver pin')
 print(json.dumps({'status':'PASS_CONDITIONAL_COMPACT44_LOW_EXACT_PRELAUNCH_AUDIT','driver_commit':'7beb48d390','driver_sha256':EXPECTED,'parent_status':check['status'],'controls':results,'scope':'Static pins and fake control flow only; separately observed full parent verify is recorded in terminal observation. No Lean build, retained-MC or graph binding, machine/checker or PRA theorem. Trusted clean initial loader, external stable-HEAD/sole-Lean window and inherited provider/resource limits required.'},indent=2))
if __name__=='__main__':main()
