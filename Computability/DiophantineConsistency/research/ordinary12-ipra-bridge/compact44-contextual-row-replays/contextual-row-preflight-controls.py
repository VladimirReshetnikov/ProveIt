#!/usr/bin/env python3
"""No-Lean controls for separate contextual inverse and exclusion drivers."""
import importlib.util,json,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[5];B=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';VIEW=Path('/tmp/ipra-historical-audit-review-01')
for directory,prefix in [('compact44-inverse-lookup-prototype','ipra-compact-inverse-contextual-pair-'),('compact44-model-noextra-prototype','ipra-compact-noextra-contextual-pair-')]:
 p=B/directory/'contextual-replay.py';sp=importlib.util.spec_from_file_location('contextual_driver',p);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.pins();orig=m.PINS;m.PINS={m.CONTEXT/'contextual-chain.py':'0'*64}
 try:
  try:m.pins();raise AssertionError('wrong context pin accepted')
  except ValueError as e:assert 'fixed input drift' in str(e)
 finally:m.PINS=orig
 for flags in (['-I','-S','-O'],[],['-S','-B'],['-I','-B']):
  q=subprocess.run([sys.executable,*flags,str(p),'--help'],capture_output=True,text=True,timeout=10);assert q.returncode and 'requires nonoptimized python3 -I -S' in q.stderr
 with tempfile.TemporaryDirectory(prefix=prefix+'control-',dir='/tmp') as d:
  q=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--output',d,'--historical-view',str(VIEW),'--expected-head','invalid'],capture_output=True,text=True,timeout=10);assert q.returncode and 'output exists' in q.stderr and not list(Path(d).iterdir())
  q=subprocess.run([sys.executable,'-I','-S','-B',str(p),'--output',d+'-new','--historical-view',str(VIEW),'--expected-head','invalid'],capture_output=True,text=True,timeout=10);assert q.returncode and 'unexpected launch HEAD' in q.stderr and not Path(d+'-new').exists()
 reviewed=json.loads((m.CONTEXT_REVIEW/'CHECK.json').read_text());row=json.loads((m.AUDIT/'CHECK.json').read_text());forbidden=json.loads((m.FORBID/'CHECK.json').read_text()) if hasattr(m,'FORBID') else None
 for mode in ('good','review_mismatch','row_mismatch','row_failure'):
  def run(cmd,**kw):
   if str(m.CONTEXT_REVIEW/'audit.py') in cmd:out={'bad':True} if mode=='review_mismatch' else reviewed
   elif str(m.CONTEXT/'contextual-chain.py') in cmd:out={'bad':True} if mode=='row_mismatch' else row
   elif hasattr(m,'FORBID') and str(m.FORBID/'audit.py') in cmd:out=forbidden
   else:raise AssertionError(('unexpected subprocess',cmd))
   return subprocess.CompletedProcess(cmd,1 if mode=='row_failure' and str(m.CONTEXT/'contextual-chain.py') in cmd else 0,stdout=json.dumps(out),stderr='')
  m.subprocess=type('Fake',(),{'run':staticmethod(run)})
  try:
   result=m.audit(VIEW)
   if mode!='good':raise AssertionError((directory,mode,'bad parent accepted'))
  except ValueError:
   if mode=='good':raise
 print(directory,'PASS pins/interpreter/output/head and contextual parent success/failures')
