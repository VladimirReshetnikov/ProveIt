#!/usr/bin/env python3
"""Read-only original/replay comparison, not an independent Lean build."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('requires python3 -I -S -B')
r=Path(__file__).resolve().parents[2]; old=r/'research/rational-carrier64-cleared-pair';p=r/'research/rational-carrier64-cleared-pair-replay';a=old/'observations/attempt01';b=p/'observations/attempt01';oa=Path('/tmp/rational-carrier64-cleared-pair-priority-check01');ob=Path('/tmp/rational-carrier64-cleared-pair-replay-priority-check01')
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
pins={old/'ClearedCurrentPair.lean':'fb35fe4a8c8bfa1995265109485853a7b906728a9e1e87140d096b415be2f079',p/'check01.py':'0ecdc2e6fcaa5809fb2cc2d258d3effd472ca6d9c5afd3d666f1ab3f1ea8b211',a/'result.json':'de1c08b733e08df60462a56f1a3640187106f3400c00654f9b5d198a4ed5e602',b/'result.json':'631e514d4cb557462890ffd2dd7b8cfacf91f83b8b67205b9f6f5e881d629a51',a/'compile.log':'9b295efdef720cee846b4f420067ae5e4ccfedbf224b67d5bf817ebbbd9e9087',b/'compile.log':'9b295efdef720cee846b4f420067ae5e4ccfedbf224b67d5bf817ebbbd9e9087',a/'outer-terminal.json':'86b0b1817754f554c1818a5a15e21ae9722238f7c8f7e81f56c0b57d606a5807',b/'outer-terminal.json':'0659fa11615658e93ba817037da27d9bc3415f2af0a127c62a3c6f63248075c0',oa/'ClearedCurrentPair.olean':'6f8afbccd823e06ce3173999dcedab7828abb573d04e7855fa40583298584cdb',ob/'ClearedCurrentPair.olean':'6f8afbccd823e06ce3173999dcedab7828abb573d04e7855fa40583298584cdb'}
for f,h in pins.items():
 if not f.is_file() or sha(f)!=h:raise ValueError(('pin',str(f)))
if (old/'ClearedCurrentPair.lean').read_bytes()!=(a/'ClearedCurrentPair.lean').read_bytes():raise ValueError('original source snapshot')
if (oa/'ClearedCurrentPair.olean').read_bytes()!=(ob/'ClearedCurrentPair.olean').read_bytes() or (a/'compile.log').read_bytes()!=(b/'compile.log').read_bytes():raise ValueError('object/log byte mismatch')
x=json.loads((a/'result.json').read_bytes());y=json.loads((b/'result.json').read_bytes())
for z,folder,tmp,session in ((x,a,oa,53951),(y,b,ob,4597)):
 if z['status']!='PASS' or z['exit']!=0 or z['stop_reason'] is not None or not z['guards_stable'] or z['guards_before']!=z['guards_after'] or z['group_rss_samples']<1:raise ValueError('terminal')
 if z['lean_memory_mib']!=2800 or '-M2800' not in z['command'] or z['sampled_peak_group_rss_bytes']>=z['sampled_group_rss_limit_bytes'] or z['minimum_memavailable_bytes']<10*1024**3:raise ValueError('resource receipt')
 if (folder/'result.json').read_bytes()!=(tmp/'result.json').read_bytes() or (folder/'compile.log').read_bytes()!=(tmp/'compile.log').read_bytes():raise ValueError('temporary copies')
 t=json.loads((folder/'outer-terminal.json').read_bytes())
 if t['session_id']!=session or t['terminal_exit_code']!=0 or t['returned_session_id'] is not None:raise ValueError('outer observation')
if x['lean_path']!=y['lean_path'] or x['command'][:-1]!=y['command'][:-1] or x['command'][-1]==y['command'][-1]:raise ValueError('command/provider comparison')
for f,v in x['guards_after'].items():
 if f not in y['guards_after'] or y['guards_after'][f]!=v:raise ValueError(('original guard differs',f))
for f,v in y['guards_after'].items():
 f=Path(f)
 if v is None:
  if os.path.lexists(f):raise ValueError(('shadow',str(f)))
 elif not f.is_file() or str(f.resolve())!=v['realpath'] or sha(f)!=v['sha256']:raise ValueError(('current guard',str(f)))
print(json.dumps({'status':'PASS_SAME_BASE_REPLAY_AUDIT','original_direct_guard_count':len(x['guards_after']),'replay_guard_count':len(y['guards_after']),'original_outer_session':53951,'replay_outer_session':4597,'identical_object_sha256':sha(ob/'ClearedCurrentPair.olean'),'identical_log_sha256':sha(b/'compile.log'),'scope':'Same-source same-base replay; no independent provider rebuild, Lean replay or transitive audit.'},sort_keys=True,indent=2))
