from pathlib import Path
import os,subprocess,time,json,importlib.util,sys
s=Path('/tmp/zfc-intake-161');r=s/'run60';e=s/'run60-evidence';e.mkdir();sys.path.insert(0,str(r/'code'))
spec=importlib.util.spec_from_file_location('suite60',r/'code/verify_all.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
m.verify_manifest=lambda:dict(status='SKIPPED_BY_USER_INTAKE_INSTRUCTION')
original=m.subprocess.run
def run(*a,**kw):
 cp=original(*a,**kw);script=Path(a[0][2]);name=script.parent.name+'-'+script.stem
 if '--zone' in a[0]:name+='-'+Path(a[0][a[0].index('--zone')+1]).stem
 (e/(name+'.stdout.log')).write_text(cp.stdout)
 if '--output' in a[0]:
  p=Path(a[0][a[0].index('--output')+1]);(e/(name+'.json')).write_bytes(p.read_bytes())
 return cp
m.subprocess.run=run
sys.argv=[str(r/'code/verify_all.py'),'--output',str(e/'verification.json')];m.main()
