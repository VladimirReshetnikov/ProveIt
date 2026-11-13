#!/usr/bin/env python3
"""Bounded read-only /proc census for one timeout-owned Lean process; no signals."""
import json,os,sys,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
out=Path('/tmp/normalized106-direct-probe-A-20261105');pidfile=out/'timeout.pid';result=out/'observer.json';ready=out/'observer-ready'
if result.exists() or ready.exists():raise SystemExit('refusing old observer output')
def record(pid):
 raw=Path('/proc',str(pid),'stat').read_text(); end=raw.rfind(')');fields=raw[end+1:].split()
 return {'pid':pid,'comm':raw[raw.find('(')+1:end],'state':fields[0],'ppid':int(fields[1]),'session':int(fields[3]),'start':int(fields[19])}
def mem():
 for l in Path('/proc/meminfo').read_text().splitlines():
  if l.startswith('MemAvailable:'):return int(l.split()[1])*1024
 raise RuntimeError('MemAvailable unavailable')
def rss(pid):
 for l in Path('/proc',str(pid),'status').read_text().splitlines():
  if l.startswith('VmRSS:'):return int(l.split()[1])*1024
 return 0
ready.write_text('ready\n');deadline=time.monotonic()+140;anchor=None;samples=0;lean_samples=0;desc={};unexpected={};peak=0;minimum=mem();failure=None;terminal=None
while time.monotonic()<deadline:
 try:
  if not pidfile.exists():time.sleep(.05);continue
  pid=int(pidfile.read_text().strip())
  try:top=record(pid)
  except FileNotFoundError:
   if anchor is not None:terminal='ANCHOR_EXITED'
   else:terminal='ANCHOR_NOT_OBSERVED'
   break
  if anchor is None:anchor=top
  if top['start']!=anchor['start']:terminal='ANCHOR_IDENTITY_CHANGED';break
  if top['state'] in ('Z','X'):terminal='ANCHOR_TERMINAL';break
  table={}
  for x in Path('/proc').iterdir():
   if not x.name.isdecimal():continue
   try:row=record(int(x.name));table[row['pid']]=row
   except (FileNotFoundError,ProcessLookupError):continue
  direct=[x for x in table.values() if x['ppid']==pid and x['state'] not in ('Z','X')]
  if len(direct)>1:
   for x in direct:unexpected[str(x['pid'])]=x
  for child in direct:
   if child['comm']=='lean':
    lean_samples+=1
    try:peak=max(peak,rss(child['pid']))
    except (FileNotFoundError,ProcessLookupError):pass
   frontier=[child['pid']];seen=set(frontier)
   while frontier:
    parent=frontier.pop()
    for x in table.values():
     if x['ppid']==parent and x['pid'] not in seen and x['state'] not in ('Z','X'):
      desc[str(x['pid'])]=x;seen.add(x['pid']);frontier.append(x['pid'])
  samples+=1;minimum=min(minimum,mem());time.sleep(.05)
 except Exception as exc:failure=repr(exc);terminal='OBSERVER_ERROR';break
if terminal is None:terminal='OBSERVER_DEADLINE'
recorded={'status':terminal,'anchor':anchor,'samples':samples,'lean_samples':lean_samples,'sampled_lean_descendants':list(desc.values()),'unexpected_direct_children':list(unexpected.values()),'sampled_peak_lean_rss_bytes':peak,'minimum_available_bytes':minimum,'error':failure,'scope':'Read-only periodic samples only; short-lived descendants and resource spikes may be missed. No signals or automatic resource stop.'}
result.write_text(json.dumps(recorded,indent=2,sort_keys=True)+'\n');print(json.dumps(recorded,sort_keys=True))
