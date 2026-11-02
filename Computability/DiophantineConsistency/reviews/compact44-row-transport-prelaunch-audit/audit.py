#!/usr/bin/env python3
"""No-Lean static and fake-loop review of bounded row transport wrapper."""
import hashlib,importlib.util,json,re,subprocess,sys
from pathlib import Path
ROOT=Path.cwd();BASE=ROOT/'Computability/DiophantineConsistency';PKG=BASE/'research/ordinary12-ipra-bridge/compact44-row-transport-prototype';DRIVER=PKG/'replay.py';EXPECTED='4030748893a24268b76ee70fb97164d9b9649b796acbad1a557e73a0b9feb80a'
def need(b,m):
 if not b:raise ValueError(m)
def main():
 name=DRIVER.relative_to(ROOT).as_posix();blob=subprocess.run(['git','show','23bd9093c8:'+name],cwd=ROOT,check=True,stdout=subprocess.PIPE).stdout
 need(hashlib.sha256(blob).hexdigest()==hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'driver bytes')
 sp=importlib.util.spec_from_file_location('row_review',DRIVER);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.pins()
 names=re.findall(r'^#print axioms\s+([^\s]+)',(PKG/'CompactRowComplete.lean').read_text(),re.M);need(names==m.NAMES and len(names)==12,'exact source report names')
 controls=[]
 for script in (str(Path(__file__).resolve().parent/'mock_loop.py'),str(Path(__file__).resolve().parent/'guards.py')):
  q=subprocess.run([sys.executable,'-I','-S','-B',script],cwd=ROOT,capture_output=True,text=True,timeout=120);need(q.returncode==0 and not q.stderr,'control '+script+' '+q.stderr);controls.append({'script':Path(script).name,'exit':q.returncode,'stdout':q.stdout})
 need('good PASS fake_children 2' in controls[0]['stdout'],'two fake children')
 need(hashlib.sha256(DRIVER.read_bytes()).hexdigest()==EXPECTED,'post driver drift')
 print(json.dumps({'status':'PASS_CONDITIONAL_COMPACT_ROW_TRANSPORT_PRELAUNCH_AUDIT','driver_commit':'23bd9093c8','driver_sha256':EXPECTED,'source_report_names':names,'controls':controls,'scope':'No Lean build. Separately observed full parent preflight is in terminal observation. Bounded local field and matching iff only; no global modeled adjacency, tiling, checker or iPRA. Requires trusted initial loader and externally enforced stable-HEAD/sole-Lean window; point-in-time and inherited provider/resource limits remain.'},indent=2))
if __name__=='__main__':main()
