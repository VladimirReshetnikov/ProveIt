#!/usr/bin/env python3
"""No-Lean controls for required direct object guards in both pair drivers."""
import importlib.util, json, tempfile
from pathlib import Path
base=Path(__file__).resolve().parents[1]
configs=[('compact44-inverse-lookup-prototype',['Init.olean','CompactRowComplete.olean']),
 ('compact44-model-noextra-prototype',['Init.olean','Compact943Data.olean']),
 ('compact44-model-noextra-prototype',['Init.olean','CompactRowComplete.olean','CompactForbidden.olean'])]
results=[]
with tempfile.TemporaryDirectory(prefix='compact-required-object-controls-') as d:
 root=Path(d)
 for ix,(directory,names) in enumerate(configs):
  p=base/directory/'replay.py';spec=importlib.util.spec_from_file_location('driver'+str(ix),p);mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
  stage=root/str(ix);stage.mkdir();paths=[stage/n for n in names]
  for f in paths:f.write_bytes(b'fake existing regular object')
  mod.require_objects({str(f) for f in paths},'control',str(ix))
  for f in paths:
   f.unlink()
   try:mod.require_objects({str(t) for t in paths},'control',str(ix));raise AssertionError('missing object accepted')
   except ValueError as e:
    if 'missing required object' not in str(e):raise
   f.write_bytes(b'fake existing regular object')
  f=paths[-1];f.unlink();f.mkdir()
  try:mod.require_objects({str(t) for t in paths},'control',str(ix));raise AssertionError('directory accepted')
  except ValueError as e:
   if 'missing required object' not in str(e):raise
  results.append({'driver':directory,'expected':names,'positive':'accepted','missing_cases_rejected':len(paths),'directory_rejected':True})
print(json.dumps({'status':'PASS_REQUIRED_OBJECT_GUARD_CONTROLS','lean_launched':False,'results':results},indent=2))
