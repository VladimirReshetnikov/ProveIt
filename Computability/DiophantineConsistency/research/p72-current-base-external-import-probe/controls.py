#!/usr/bin/env python3
import importlib.util,json,os,signal,subprocess,sys,tempfile
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
P=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('monitor',P/'monitor.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def need(v,s):
 if not v:raise RuntimeError(s)
bystander=subprocess.Popen([sys.executable,'-I','-S','-B','-c','import time;time.sleep(30)'],start_new_session=True)
bystander_fd=os.open("/proc/"+str(bystander.pid),os.O_RDONLY|os.O_DIRECTORY)
with tempfile.TemporaryDirectory(prefix='thirteen-monitor-controls-') as d:
 env=dict(os.environ);base=[sys.executable,'-I','-S','-B','-c'];n=0
 def case(code,**kw):
  global n
  n+=1;return m.run(base+[code],d,env,str(Path(d)/str(n)),**kw)
 opts=dict(rss_limit=1024**3,mem_floor=1,seconds=2,interval=.02)
 ok=case('print(42)',**opts);need(ok['exit']==0 and ok['stop_reason'] is None and not ok['monitor_errors'],'success')
 timeout=case('import time;time.sleep(10)',rss_limit=1024**3,mem_floor=1,seconds=.2,interval=.02);need(timeout['stop_reason']=='timeout' and timeout['exit'] is not None,'timeout')
 low=case('import time;time.sleep(10)',rss_limit=1024**3,mem_floor=m.mem_available()+1024**3,seconds=2,interval=.02);need(low['stop_reason']=='host_memory_floor' and low['exit'] is not None,'host floor')
 high=case('import time; x=bytearray(16000000);time.sleep(10)',rss_limit=4*1024**2,mem_floor=1,seconds=2,interval=.02);need(high['stop_reason']=='session_rss_limit' and high['exit'] is not None,'rss')
 desc=case('import subprocess,time;subprocess.Popen(["sleep","10"]);time.sleep(10)',rss_limit=1024**3,mem_floor=1,seconds=2,interval=.02);need(desc['stop_reason']=='unexpected_descendant' and desc['observed_descendant_pids'] and desc['exit'] is not None,'descendant')
 need(all(not x['monitor_errors'] for x in (ok,timeout,low,high,desc)),'monitor errors')
 need(bystander.poll() is None,'outside-session bystander')
 m.send(bystander_fd,signal.SIGTERM);bystander.wait(timeout=2);os.close(bystander_fd)
 print(json.dumps({'outside_session_bystander_untouched':True,'status':'PASS_SYNTHETIC_MONITOR_CONTROLS','cases':{'success':ok,'timeout':timeout,'host_floor':low,'session_rss':high,'descendant':desc},'scope':'synthetic child processes only; sampled limits and scan races apply'},indent=2,sort_keys=True))
