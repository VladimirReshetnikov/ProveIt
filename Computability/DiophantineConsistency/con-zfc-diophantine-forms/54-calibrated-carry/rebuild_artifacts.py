#!/usr/bin/env python3
"""Rebuild declared polynomial data in an isolated copy and compare exact bytes."""
import sys
if not __debug__ or sys.flags.optimize:raise SystemExit('REJECT optimized Python')
import os,pathlib,subprocess,tempfile,shutil,hashlib,json
R=pathlib.Path(__file__).resolve().parent

def main():
 env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env['PYTHONDONTWRITEBYTECODE']='1'
 subprocess.run([sys.executable,'-B',str(R/'verify_release.py'),'--integrity-only'],check=True,env=env)
 selected=['source/selective12_source.json','source/all31_source.json','nine/METRICS.json','nine/FIXED_BINDING.json','integer/METRICS.json','integer/FIXED_BINDING.json','integer/SOURCE_BOUNDS.json','positive/SHORT_BUILD_RECEIPT.json']
 for pattern in ['packing/CERTIFICATE_*.json','nine/generated/*.json','nine/fixed/*.gz','integer/generated/*.json','integer/fixed/*.gz','positive/p*.json','positive/comparisons/*.json']:
  selected += [p.relative_to(R).as_posix()for p in sorted(R.glob(pattern))]
 expected={n:hashlib.sha256((R/n).read_bytes()).hexdigest()for n in selected}
 commands=[['source/build_selective_source.py'],['packing/build_certificates.py','packed163.txt','packed170.txt','packed174.txt'],['nine/build_nine.py'],['nine/materialize_fixed.py'],['integer/build_integer.py'],['positive/build_short.py']]
 with tempfile.TemporaryDirectory(prefix='proveit-calibrated-rebuild-')as td:
  work=pathlib.Path(td)/'release';shutil.copytree(R,work)
  for cmd in commands:
   print('REBUILD '+' '.join(cmd),flush=True)
   subprocess.run([sys.executable,'-B',str(work/cmd[0]),*cmd[1:]],cwd=work,check=True,env=env)
  for n,sha in expected.items():
   if hashlib.sha256((work/n).read_bytes()).hexdigest()!=sha:raise RuntimeError('REBUILD BYTE DIFFERENCE: '+n)
 print(json.dumps({'status':'PASS','reproduced_files':len(expected),'scope':'Exact byte-identical source/certificate/graph/fixed-leaf regeneration in the tested Python/SymPy environment; PDF and proof texts are source artifacts, not regenerated here.'},indent=2))
if __name__=='__main__':main()
