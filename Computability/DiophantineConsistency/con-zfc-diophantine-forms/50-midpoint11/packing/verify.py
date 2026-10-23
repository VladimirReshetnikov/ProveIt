#!/usr/bin/env python3
"""Rebuild and audit the support-aware package using Python standard library."""
from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path(__file__).resolve().parent
def main():
 pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
 checked=0
 for r in pins['records']:
  if 'sha256' in r:
   assert hashlib.sha256((ROOT/r['local_path']).read_bytes()).hexdigest()==r['sha256'],r['local_path'];checked+=1
 for script in ['code/build.py','nine/build_multitarget_nine.py','code/verify_support.py','code/audit_nine.py']:
  subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,check=True)
 result=subprocess.run([sys.executable,str(ROOT/'code/audit_full_circuit.py')],cwd=ROOT,check=True,capture_output=True,text=True)
 sun=json.loads(result.stdout);assert sun['status']=='PASS'
 (ROOT/'certificates/sun_formula_replay.json').write_text(result.stdout)
 report={'status':'PASS','baseline_commit':pins['baseline_commit'],'verbatim_source_files_checked':checked,'sun10':{'integer_variables':10,'degree':56593864,'binary_operations':653},'jones9':{'positive_variables':9,'degree':30947584,'binary_operations':651},'natural_variant_operations':654,'full_kernel_formalization':False,'semantic_dependencies':'Pinned native-window/Pell compiler and K215 endpoint; Jones ratio theorem; Sun ten-integer theorem for Sun10 only.'}
 (ROOT/'certificates/release_verification.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':
 if not __debug__:raise SystemExit('Run without -O; assertions are part of the finite checks.')
 main()
