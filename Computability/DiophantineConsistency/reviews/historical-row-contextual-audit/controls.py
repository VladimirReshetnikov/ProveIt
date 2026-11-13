#!/usr/bin/env python3
"""No-Lean fail-closed controls for the contextual row-parent runner."""
import hashlib,importlib.util,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4];P=Path(__file__).resolve().parent/'contextual-chain.py'
s=importlib.util.spec_from_file_location('context_review',P);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
def reject(args,fragment):
 old=sys.argv;sys.argv=[str(P),*args]
 try:
  try:m.main();raise AssertionError('bad control accepted')
  except (ValueError,FileNotFoundError) as e:
   if fragment not in str(e):raise
 finally:sys.argv=old
reject(['bad','/tmp/ipra-historical-audit-review-01'],'usage:')
reject(['row','/tmp'],'invalid cwd or historical view')
old=m.TARGETS['row'];m.TARGETS['row']=(old[0],'0'*64)
try:reject(['row','/tmp/ipra-historical-audit-review-01'],'original audit byte drift')
finally:m.TARGETS['row']=old
with tempfile.TemporaryDirectory(prefix='ipra-historical-audit-review-control-',dir='/tmp') as d:
 view=Path(d);plan=view/'Computability/DiophantineConsistency/reviews/thirteen-model-endpoint-closure-independent-audit';plan.mkdir(parents=True)
 original=Path('/tmp/ipra-historical-audit-review-01/Computability/DiophantineConsistency/reviews/thirteen-model-endpoint-closure-independent-audit')
 for n in ('audit.py','CHECK.json'):shutil.copyfile(original/n,plan/n)
 source=view/'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ModelCarrierCurrent.lean';source.parent.mkdir(parents=True);source.write_text('wrong source')
 reject(['row',str(view)],'historical view drift')
for flags in (['-I','-S','-O'],[],['-S','-B'],['-I','-B']):
 q=subprocess.run([sys.executable,*flags,str(P),'row','/tmp/ipra-historical-audit-review-01'],capture_output=True,text=True,timeout=10)
 if not q.returncode or 'requires nonoptimized python3 -I -S' not in q.stderr:raise ValueError('interpreter guard')
print('PASS_TARGET_CWD_ORIGINAL_AUDIT_HISTORICAL_SOURCE_AND_INTERPRETER_CONTROLS')
