#!/usr/bin/env python3
"""No-Lean controls for the driver's fixed-pin verifier."""
import hashlib,importlib.util,json,os,sys,tempfile
from pathlib import Path
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated nonoptimized Python required')
HERE=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('driver',HERE/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();results=[]
with tempfile.TemporaryDirectory(prefix='halt-pin-fake-') as tmp:
 root=Path(tmp);plan=root/'plan';plan.mkdir();fixed=root/'fixed';fixed.mkdir();m.PLAN=plan;m.PINS={'a':None,'b':None};m.FIXED={}
 for n in m.PINS:(plan/n).write_text(n);m.PINS[n]=H(plan/n)
 for n in ('c','d'):
  p=fixed/n;p.write_text(n);m.FIXED[p]=H(p)
 m.validate_fixed();results.append('matching pins accepted')
 for p in [plan/'a',plan/'b',fixed/'c',fixed/'d']:
  original=p.read_bytes();p.write_bytes(original+b'!')
  try:m.validate_fixed()
  except ValueError:results.append('drift rejected '+p.name)
  else:raise RuntimeError('drift accepted '+str(p))
  p.write_bytes(original);p.unlink()
  try:m.validate_fixed()
  except ValueError:results.append('missing rejected '+p.name)
  else:raise RuntimeError('missing accepted '+str(p))
  p.write_bytes(original);target=p.with_name(p.name+'-same');target.write_bytes(original);p.unlink();p.symlink_to(target)
  try:m.validate_fixed()
  except ValueError:results.append('matching-content symlink rejected '+p.name)
  else:raise RuntimeError('matching-content symlink accepted '+str(p))
  p.unlink();p.write_bytes(original);target.unlink()
print(json.dumps({'status':'PASS_NO_LEAN_FIXED_PIN_CONTROLS','checks':results,'total':len(results),'lean_launched':False},indent=2,sort_keys=True))
