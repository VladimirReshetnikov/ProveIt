#!/usr/bin/env python3
"""Inspect and mock a pinned read-only Python observer. Never launch Lean."""
import ast,hashlib,json,runpy,sys,types
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary14-natural79-readonly-runtime-preflight'
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b
source=pin(P/'preflight.py','9321dc243e25798784183bb0a58e84856a34db8bdd3843e1c96c5b36c9955de2')
receipt=json.loads(pin(P/'static.json','3c7066e21fbd4ab199f3cb728c9be64af30e788f66bb4216aa7bef975a96e3ae'))
tree=ast.parse(source)
# Exact audited imports and call sites: rejects any new process or write API.
imports=[]
for node in ast.walk(tree):
 if isinstance(node,ast.Import):imports.extend(a.name for a in node.names)
 if isinstance(node,ast.ImportFrom):imports.append(node.module)
assert sorted(imports)==sorted(['pathlib','hashlib','json','os','re','sys'])
calls={ast.unparse(n.func) for n in ast.walk(tree) if isinstance(n,ast.Call)}
allowed={"(ROOT / 'lean-toolchain').read_bytes","(p / 'cmdline').read_bytes",'Path',"Path('/proc').iterdir",'Path(__file__).resolve','ValueError','deps.extend','hashlib.sha256','hashlib.sha256(b).hexdigest','int','json.dumps','json.loads','len','line.split','line.startswith','line.strip','matches.append','observe','os.fsdecode','os.readlink','os.stat','os.statvfs','outputs.add','p.is_file','p.is_symlink','p.name.isdigit','p.read_bytes','p.resolve','pinned','print','raw.decode','raw.decode().splitlines','raw.split','re.fullmatch','records.values','seen.add','set','sha','sorted','static','str','sys.exit','type'}
assert calls==allowed,(calls-allowed,allowed-calls)
assert not any(isinstance(n,(ast.With,ast.AsyncWith,ast.Delete,ast.Global,ast.Nonlocal)) for n in ast.walk(tree))
assert receipt['stage_files_and_headers_checked']==201 and receipt['project_frontier_records_checked']==41 and receipt['external_frontier_records_checked']==6
assert receipt['launch_authorized'] is False and receipt['launch_supported'] is False
# Loading as a non-main module executes only definitions and constants. Its AST
# above is pinned and audited; replace all system access in observe with fakes.
ns=runpy.run_path(str(P/'preflight.py'),run_name='reviewed_not_main')
fn=ns['observe'];g=fn.__globals__; realpath=Path
class ProcEntry:
 def __init__(self,n):self.name=n
 def __truediv__(self,x):return ProcFile(self.name,x)
class ProcFile:
 def __init__(self,n,x):self.n=n;self.x=x
 def read_bytes(self):
  assert self.x=='cmdline'
  if self.n=='4':raise PermissionError('test cmdline denial')
  return {'1':b'/bin/lean\0--version\0','2':b'/usr/bin/wrapper\0','3':b'lean\0'}[self.n]
class Proc:
 def iterdir(self):return [ProcEntry('1'),ProcEntry('2'),ProcEntry('3'),ProcEntry('4'),ProcEntry('5'),ProcEntry('not-a-pid')]
def fake_path(x):return Proc() if str(x)=='/proc' else realpath(x)
def readlink(p):
 if p.n=='5':raise FileNotFoundError('test disappeared')
 return {'1':'/opt/lean','2':'/opt/lake','3':'/bin/wrapper','4':'/bin/lean'}[p.n]
FLOOR=5_100_000_000
free={'workspace':FLOOR,'temporary':FLOOR+1}
def statvfs(path):
 key='temporary' if str(path)=='/tmp' else 'workspace'
 return types.SimpleNamespace(f_bavail=free[key],f_frsize=1)
fakeos=types.SimpleNamespace(readlink=readlink,fsdecode=lambda b:b.decode(),statvfs=statvfs,stat=lambda p:types.SimpleNamespace(st_dev=1))
g['Path']=fake_path;g['os']=fakeos
obs=fn();ps=obs['process_scan']
assert ps['scanned']==3 and ps['inaccessible_or_disappeared']==2
assert [m['pid'] for m in ps['exact_lean_lake_executable_or_argv0_matches']]==[1,2,3]
assert obs['filesystem']['workspace']['above_strict_floor'] is False
assert obs['filesystem']['temporary']['above_strict_floor'] is True
assert not obs['launch_supported'] and not obs['launch_authorized'] and not obs['atomic_reservation']
free['workspace']=FLOOR-1;free['temporary']=FLOOR
obs=fn();assert not obs['filesystem']['workspace']['above_strict_floor'] and not obs['filesystem']['temporary']['above_strict_floor']
# Failure in top-level process enumeration or filesystem calls propagates to
# the executable's outer failure handler; it is not treated as an idle result.
class BadProc:
 def iterdir(self):raise PermissionError('proc unavailable')
g['Path']=lambda x: BadProc() if str(x)=='/proc' else realpath(x)
try:fn();raise AssertionError('missing proc failure')
except PermissionError:pass
g['Path']=fake_path
fakeos.statvfs=lambda p: (_ for _ in ()).throw(OSError('statvfs unavailable'))
try:fn();raise AssertionError('missing statvfs failure')
except OSError:pass
print(json.dumps({'scope':'pinned Python AST and mocked observer controls; no Lean, subprocess, or actual filesystem mutation',
 'process_matches_mocked':3,'per_process_failures_counted':2,'top_level_failures_propagate':True,
 'strict_floor_controls':['floor-1 false','floor false','floor+1 true'],
 'observer_is_enforceable_launch_guard':False,'static_receipt_reproduced_separately':True},sort_keys=True,indent=2))
