#!/usr/bin/env python3
"""Exercise actual verify() receipt schemas with fake no-Lean audit subprocesses."""
import hashlib,importlib.util,json,subprocess,tempfile
from pathlib import Path
p=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('replay',p/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
original=m.CLOSURE_AUDIT;closure=json.loads((original/'CHECK.json').read_bytes());obs=json.loads((original/'terminal-observation.json').read_bytes());h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();small=['status','reviewed_commit','scan_sha256','source_modules','named_reports','parent_objects_per_side','old_overlap_per_side','old_differing_per_side','external_direct_slots','target_slots','package_slots','source_rows','parent_audit_rerun_exit','lean_launched'];modes=[('good',None)]+[(kind,key) for key in small for kind in ('missing','wrong')]+[('bool_exit','parent_audit_rerun_exit')]
for kind,key in modes:
 with tempfile.TemporaryDirectory(prefix='fixed-clean-schema-',dir='/tmp') as td:
  c=dict(closure);o=dict(obs)
  if kind=='missing':del c[key]
  elif kind=='wrong':c[key]='conflicting-value'
  elif kind=='bool_exit':c[key]=False
  d=Path(td);(d/'CHECK.json').write_text(json.dumps(c));(d/'audit.py').write_text('# fake audit\n');o['check_sha256']=h(d/'CHECK.json');(d/'terminal-observation.json').write_text(json.dumps(o));old=m.CLOSURE_AUDIT;m.CLOSURE_AUDIT=d
  saved=dict(m.PINS);m.PINS={k:v for k,v in saved.items() if k.parent!=old};m.PINS.update({d/'CHECK.json':h(d/'CHECK.json'),d/'audit.py':h(d/'audit.py'),d/'terminal-observation.json':h(d/'terminal-observation.json')})
  def run(cmd,**kwargs):
   path=Path(cmd[-1]);out=(d/'CHECK.json').read_bytes() if path==d/'audit.py' else (m.PLAN/'scan.json').read_bytes() if path==m.PLAN/'scan.py' else (m.PARENT_AUDIT/'CHECK.json').read_bytes() if path==m.PARENT_AUDIT/'audit.py' else None
   assert out is not None,cmd
   return subprocess.CompletedProcess(cmd,0,stdout=out,stderr=b'')
  original_run=m.subprocess.run;m.subprocess.run=run
  try:
   try:m.verify();error=None
   except ValueError as e:error=str(e)
   if kind=='good':assert error is None,error
   else:assert error is not None and 'invalid closure receipt' in error,(kind,key,error)
   print(kind,key,'PASS')
  finally:m.subprocess.run=original_run;m.PINS=saved;m.CLOSURE_AUDIT=old
