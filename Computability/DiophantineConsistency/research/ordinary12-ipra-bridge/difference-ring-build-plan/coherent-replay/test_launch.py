#!/usr/bin/env python3
"""Negative and fake-process launcher controls; never starts a real build."""
import contextlib,importlib.util,io,json,os,subprocess,sys,tempfile
from pathlib import Path
p=Path(__file__).with_name('launch.py');s=importlib.util.spec_from_file_location('toy_launcher',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
for flags,env_extra in (([],{'PYTHONOPTIMIZE':'1'}),(['-O'],{})):
 env=os.environ.copy();env.pop('PYTHONOPTIMIZE',None);env.update(env_extra)
 proc=subprocess.run([sys.executable,*flags,str(p)],env=env,text=True,capture_output=True)
 assert proc.returncode!=0 and 'rejects optimized' in proc.stderr
 assert not m.OUTPUT.exists() and not m.PREFLIGHT.exists() and not m.TERMINAL.exists()
print('PASS actual optimized launcher rejected before writes')
old=m.PINS
try:
 m.PINS={Path('/definitely-not-a-valid-pinned-input'):'0'*64}
 try:m.preflight()
 except (FileNotFoundError,ValueError):pass
 else:raise AssertionError('missing pin accepted')
finally:m.PINS=old
print('PASS missing executable pin rejected before launch')
with tempfile.TemporaryDirectory(prefix='ipra-launch-toy-') as td:
 root=Path(td);m.PREFLIGHT=root/'preflight.json';m.TERMINAL=root/'terminal.json';m.OUTPUT=root/'pair'
 m.preflight=lambda:{'status':'PASS_PINNED_COEXISTENCE_PREFLIGHT','toy':True}
 old_argv=sys.argv;sys.argv=[str(p)];captured={}
 class ToyProc:
  pid=99999999;returncode=0
  def __init__(self,cmd,**kwargs):captured.update(cmd=cmd,kwargs=kwargs)
  def communicate(self):return ('MATCHED_PASS 70 rows\n','')
 old_popen=m.subprocess.Popen;m.subprocess.Popen=ToyProc
 try:
  with contextlib.redirect_stdout(io.StringIO()) as stdout:code=m.main()
 finally:m.subprocess.Popen=old_popen;sys.argv=old_argv
 assert code==0 and m.PREFLIGHT.is_file() and m.TERMINAL.is_file()
 t=json.loads(m.TERMINAL.read_text());assert t['outer_exit_code']==0 and t['stdout']=='MATCHED_PASS 70 rows\n'
 assert captured['kwargs']['start_new_session'] and 'PYTHONOPTIMIZE' not in captured['kwargs']['env']
 assert captured['cmd'][0]==sys.executable and '-O' not in captured['cmd'] and '--expected-axiom-reports' in captured['cmd']
print('PASS fake coordinator records exit/stdout and sanitized environment')
print('PASS_COHERENT_LAUNCHER_TOY_CONTROLS')
