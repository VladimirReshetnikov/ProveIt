#!/usr/bin/env python3
"""Sample an owned session and signal only opened /proc process handles."""
import ctypes, errno, os, platform, shutil, signal, subprocess, sys, time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
if sys.platform!='linux' or platform.machine()!='x86_64':raise SystemExit('unsupported platform')
libc=ctypes.CDLL(None,use_errno=True);libc.syscall.restype=ctypes.c_long
PAGE=os.sysconf('SC_PAGE_SIZE')
def mem_available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('missing MemAvailable')
def send(fd,sig):
 r=libc.syscall(ctypes.c_long(424),ctypes.c_int(fd),ctypes.c_int(sig),ctypes.c_void_p(0),ctypes.c_uint(0))
 if r<0:raise OSError(ctypes.get_errno(),os.strerror(ctypes.get_errno()))
def scan(session,sig=None):
 found=[];errors=[]
 for p in Path('/proc').iterdir():
  if not p.name.isdecimal():continue
  fd=None
  try:
   fd=os.open(str(p),os.O_RDONLY|os.O_DIRECTORY)
   f=os.open('stat',os.O_RDONLY,dir_fd=fd)
   try: raw=os.read(f,8192).decode()
   finally:os.close(f)
   fields=raw.rsplit(')',1)[1].split();sid=int(fields[3])
   if sid!=session:continue
   item={'pid':int(p.name),'state':fields[0],'pgid':int(fields[2]),'rss':max(0,int(fields[21]))*PAGE};found.append(item)
   if sig is not None and item['state'] not in ('Z','X'):send(fd,sig)
  except (OSError,ValueError,IndexError) as e:
   if not isinstance(e,OSError) or e.errno not in (errno.ENOENT,errno.ESRCH):errors.append([p.name,repr(e)])
  finally:
   if fd is not None:os.close(fd)
 return found,errors
def terminal(pid):return os.waitid(os.P_PID,pid,os.WEXITED|os.WNOHANG|os.WNOWAIT) is not None
def run(argv,cwd,env,log,*,rss_limit,mem_floor,disk_floor,seconds,interval=.1):
 if rss_limit<=0 or mem_floor<=0 or disk_floor<=0 or seconds<=0 or interval<=0:raise ValueError('bad limits')
 p=None;reason=None;issues=[];observed=set();peak=0;lowest=None;lowest_disk=None;samples=0;started=time.monotonic();finished=False
 try:
  with open(log,'xb') as f:
   p=subprocess.Popen(argv,cwd=cwd,env=env,stdin=subprocess.DEVNULL,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
   while True:
    alive=not terminal(p.pid);members,errors=scan(p.pid);samples+=1
    if errors:issues+=errors;reason='proc_scan_error';break
    rss=sum(x['rss'] for x in members if x['state'] not in ('Z','X'));peak=max(peak,rss)
    mem=mem_available();lowest=mem if lowest is None else min(lowest,mem)
    others=[x for x in members if x['pid']!=p.pid and x['state'] not in ('Z','X')];observed.update(x['pid'] for x in others)
    if others:reason='unexpected_descendant';break
    if rss>=rss_limit:reason='session_rss_limit';break
    if mem<mem_floor:reason='host_memory_floor';break
    disk=shutil.disk_usage(cwd).free;lowest_disk=disk if lowest_disk is None else min(lowest_disk,disk)
    if disk<=disk_floor:reason='disk_floor';break
    if time.monotonic()-started>=seconds:reason='timeout';break
    if not alive:
     if not any(x['pid']==p.pid for x in members):reason='leader_not_observed';break
     finished=True;break
    time.sleep(interval)
 except BaseException as e:
  issues.append(['monitor_exception',repr(e)]);reason=reason or 'monitor_exception'
 finally:
  if p is not None:
   if not finished:
    deadline=time.monotonic()+8
    while time.monotonic()<deadline:
     members,errors=scan(p.pid,signal.SIGTERM if time.monotonic()<deadline-5 else signal.SIGKILL);issues+=errors
     observed.update(x['pid'] for x in members if x['pid']!=p.pid)
     members,errors=scan(p.pid);issues+=errors
     if not [x for x in members if x['pid']!=p.pid and x['state'] not in ('Z','X')] and terminal(p.pid):break
     time.sleep(.05)
   try:rc=p.wait(timeout=2)
   except BaseException as e:issues.append(['wait_failure',repr(e)]);rc=None
  else:rc=None
 return {'exit':rc,'stop_reason':reason,'elapsed_seconds':round(time.monotonic()-started,3),'samples':samples,'peak_session_rss_bytes':peak,'min_host_available_bytes':lowest,'min_disk_free_bytes':lowest_disk,'disk_floor_bytes':disk_floor,'observed_descendant_pids':sorted(observed),'monitor_errors':issues,'sampling_interval_seconds':interval,'rss_limit_bytes':rss_limit,'host_floor_bytes':mem_floor,'timeout_seconds':seconds,'scope':'Sampled session RSS; stable proc-handle signals; transient/escaped descendants and spikes may be missed.'}
