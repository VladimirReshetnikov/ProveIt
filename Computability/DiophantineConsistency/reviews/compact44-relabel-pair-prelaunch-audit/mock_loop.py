import contextlib,hashlib,importlib.util,io,os,shutil,subprocess,sys,tempfile
from pathlib import Path
DRIVER=Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-relabel-pair-prototype/replay.py').resolve()
if hashlib.sha256(DRIVER.read_bytes()).hexdigest()!='f2d574483b92a6648462a2700a23e2884ea5572c8f5b2162ccf6b068c9d61510':raise ValueError('driver drift')
def need(b,m):
 if not b:raise ValueError(m)
def run(mode):
 spec=importlib.util.spec_from_file_location('relabel_driver',DRIVER);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
 m.check_head=lambda:None;m.check_pins=lambda:None;m.audit=lambda:{'fake':True}
 parent=Path(tempfile.mkdtemp(prefix='relabel58-review-control-',dir='/tmp'));fake=parent/'monitor.py'
 fake.write_text('''import re\nfrom pathlib import Path\ndef monitored(cmd,env,log,timeout=600):\n src=Path(cmd[-3]);obj=Path(cmd[-1]);name=src.stem;obj.write_bytes(('FAKE_'+name).encode());lines=[]\n for d in re.findall(r'^#print axioms\\s+([A-Za-z0-9_.]+)\\s*$',src.read_text(),re.M):\n  if d.endswith(('.rows_length','.row_widths')) or re.fullmatch(r'CompactRelabelDraft.forward_\\d\\d',d):a=set()\n  elif d.endswith(('.row_bounds','.forward_roundtrip')):a={'propext','Quot.sound'}\n  else:a={'propext','Classical.choice','Quot.sound'}\n  if MODE=='wrong_axiom' and d.endswith('.row_bounds'):a={'propext'}\n  lines.append("'"+d+"' depends on axioms: ["+', '.join(sorted(a))+"]" if a else "'"+d+"' does not depend on any axioms")\n if MODE=='warning' and name=='Compact943Data':lines.append('warning: injected')\n log.write_text(('\\n'.join(lines)+'\\n') if lines else '')\n return 0,123,None\n'''.replace('MODE==',repr(mode)+'=='))
 m.MONITOR=fake
 calls=[]
 def fake_run(cmd,env=None,text=None,capture_output=None,timeout=None,**kw):
  need('--deps' in cmd,'unexpected subprocess');src=Path(cmd[-1]);lib,pkg=map(Path,env['LEAN_PATH'].split(':'));calls.append(src.stem)
  import re
  imports=re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$',src.read_text(),re.M);deps=[str(pkg/'Init.olean')]+[str(lib/Path(*d.split('.')).with_suffix('.olean')) for d in imports]
  if mode=='wrong_deps' and src.stem=='Compact943Data':deps.append('/tmp/unexpected.olean')
  return subprocess.CompletedProcess(cmd,0,stdout='\n'.join(deps)+'\n',stderr='')
 class FakeSubprocess:run=staticmethod(fake_run)
 m.subprocess=FakeSubprocess
 output=Path(tempfile.mkdtemp(prefix='ipra-compact-relabel-pair-review-',dir='/tmp'));output.rmdir();old=sys.argv;sys.argv=[str(DRIVER),'--output',str(output),'--expected-head','0'*40]
 try:
  with contextlib.redirect_stdout(io.StringIO()):
   try:m.main();err=None
   except Exception as e:err=str(e)
  if mode=='good':
   need(err is None and len(calls)==116,'full loop '+str((len(calls),err)))
  else:
   expected={'wrong_axiom':'unexpected axiom set','warning':'compiler failure','wrong_deps':'dependency mismatch'}[mode];need(err and expected in err,'control '+mode+': '+str(err))
  print(mode,'PASS fake_children',len(calls))
 finally:sys.argv=old;shutil.rmtree(output,ignore_errors=True);shutil.rmtree(parent,ignore_errors=True)
for x in ('good','wrong_axiom','warning','wrong_deps'):run(x)
