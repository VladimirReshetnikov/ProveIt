#!/usr/bin/env python3
"""Clean portable replay; no source workspace modifications other than result."""
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
names=['METRICS.json']+[p.name for p in sorted(ROOT.glob('free_whole_center11_*.json'))]
before={n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in names}
with tempfile.TemporaryDirectory(prefix='conzfc-centers-') as td:
 target=Path(td)/'scalar'
 shutil.copytree(ROOT,target,ignore=shutil.ignore_patterns('__pycache__','research','REPLAY.json'))
 runs=[]
 for args in [['build.py'],['check.py'],['-O','check.py'],['audit_mutations.py'],['-O','audit_mutations.py'],['check_scalar_top_forms.py','--graph','free_whole_center11_c300.json','--output','SCALAR_TOP_FORMS_NORMAL.json'],['-O','check_scalar_top_forms.py','--graph','free_whole_center11_c300.json','--output','SCALAR_TOP_FORMS_OPTIMIZED.json']]:
  p=subprocess.run([sys.executable,*args],cwd=target,capture_output=True,text=True)
  if p.returncode:raise RuntimeError('clean replay failed '+str(args)+'\n'+p.stdout+p.stderr)
  runs.append({'command':['python',*args],'exit_code':0})
 after={n:hashlib.sha256((target/n).read_bytes()).hexdigest() for n in names}
 if before!=after:raise ValueError('byte-identical circuit replay mismatch')
 for name in ['CHECK.json','CHECK_OPTIMIZED.json','MUTATIONS.json','MUTATIONS_OPTIMIZED.json']:
  if json.loads((target/name).read_text())['status']!='PASS':raise ValueError(name)
 out={'status':'PASS','clean_temporary_copy':True,'no_research_imported':True,'byte_identical_rebuilt_artifacts':before,'runs':runs}
(ROOT/'REPLAY.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
