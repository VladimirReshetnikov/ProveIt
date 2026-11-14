#!/usr/bin/env python3
"""Offline reproduction of the PA194QH construction and certificates."""
from pathlib import Path
import hashlib,json,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
EXPECTED='0f101f654f69230744e8c9aac14a7616745e247855fd964530603ea1ac6412ba'
def main():
 if not __debug__ or sys.flags.optimize:raise SystemExit('Run without Python -O or PYTHONOPTIMIZE.')
 for name,digest in json.loads((ROOT/'INPUT_HASHES.json').read_text()).items():
  assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,('input identity mismatch',name)
 jobs=[['construction/build_qh.py'],['verification/check_commands.py'],
  ['verification/audit_source.py','--candidate','machine','--output','machine/source_audit.json'],
  ['verification/check_literal.py','machine'],
  ['comparison/verify_novelty.py','machine/machine.tm','--output','comparison/pa194qh_novelty.json']]
 results=[]
 for args in jobs:
  print('RUN',*args,flush=True);start=time.monotonic()
  subprocess.run([sys.executable,'-B',*args],cwd=ROOT,check=True)
  results.append({'command':[sys.executable,'-B',*args],'status':'PASS','elapsed_seconds':round(time.monotonic()-start,3)})
 assert hashlib.sha256((ROOT/'machine/machine.tm').read_bytes()).hexdigest()==EXPECTED
 assert json.loads((ROOT/'machine/independent/receipt.json').read_text())['dense_sha256']==EXPECTED
 assert json.loads((ROOT/'comparison/pa194qh_novelty.json').read_text())['candidate']['structurally_new']
 result={'status':'PASS','family':'PA194QH','dense_sha256':EXPECTED,'input_files_checked':len(json.loads((ROOT/'INPUT_HASHES.json').read_text())),'stages':results,'kernel_checked':False}
 (ROOT/'verification_release.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
