#!/usr/bin/env python3
"""Read-only observations only. No subprocesses, Lean, materialization or launch."""
from pathlib import Path
import hashlib,json,os,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1];PLAN=D/'research/ordinary14-natural79-corrected-ordered-provider-plan/plan.json'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
EXPECTED_PLAN='deb0854620b8fb85461df791c545f43c09814b566ec4685517efa1696d46b035'
EXPECTED_LEAN='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
FLOOR=5_100_000_000
def sha(b):return hashlib.sha256(b).hexdigest()
def pinned(p,h):
 raw=p.read_bytes()
 if sha(raw)!=h:raise ValueError('sha256 mismatch: '+str(p))
 return raw
def static():
 plan=json.loads(pinned(PLAN,EXPECTED_PLAN))
 assert (ROOT/'lean-toolchain').read_bytes()==b'leanprover/lean4:v4.32.0\n'
 pinned(LEAN,EXPECTED_LEAN)
 stages=plan['candidate_stages'];proj=plan['selected_project_frontier_sources_and_objects'];ext=plan['selected_external_cut_sources_and_objects']
 assert len(stages)==201 and len(proj)==41 and len(ext)==6
 seen=set(proj)|set(ext);outputs=set()
 for r in stages:
  name=r['module'];assert name not in seen
  p=D/r['source'];assert p.is_file()
  raw=pinned(p,r['source_sha256']);deps=[]
  for line in raw.decode().splitlines():
   line=line.strip()
   if not line:continue
   if not line.startswith('import '):break
   assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*',line),name
   deps.extend(line.split()[1:])
  assert deps==r['lexical_imports'] and set(deps)<=seen
  assert r['unreserved_output_name'] not in outputs
  outputs.add(r['unreserved_output_name']);seen.add(name)
 assert stages[-1]['module']=='Natural79Endpoint'
 for records in (proj,ext):
  for r in records.values():
   for typ in ('source','object'):
    x=r[typ];p=Path(x['path']);assert p.is_file() and str(p.resolve(strict=True))==x['realpath'] and p.is_symlink()==x['symlink'];pinned(p,x['sha256'])
 return {'mode':'static','plan_sha256':EXPECTED_PLAN,'lean_toolchain_file':'leanprover/lean4:v4.32.0','observed_lean_binary_sha256':EXPECTED_LEAN,
 'stage_files_and_headers_checked':len(stages),'project_frontier_records_checked':len(proj),'external_frontier_records_checked':len(ext),
 'launch_authorized':False,'launch_supported':False,'result':'bounded pinned observations pass; never build authorization'}
def observe():
 # /proc observations are inherently racy and may be restricted. A disappearing
 # process is explicitly counted as inaccessible, never interpreted as idle.
 matches=[];inaccessible=0;scanned=0
 for p in sorted(Path('/proc').iterdir(),key=lambda p:p.name):
  if not p.name.isdigit():continue
  try:
   exe=os.readlink(p/'exe');raw=(p/'cmdline').read_bytes();scanned+=1
   argv0=os.fsdecode(raw.split(b'\0',1)[0]) if raw else ''
   if Path(exe).name in {'lean','lake'} or Path(argv0).name in {'lean','lake'}:
    matches.append({'pid':int(p.name),'exe':exe,'argv0':argv0})
  except (OSError,PermissionError):inaccessible+=1
 fs={}
 for label,path in (('workspace',ROOT),('temporary',Path('/tmp'))):
  s=os.statvfs(path);free=s.f_bavail*s.f_frsize
  fs[label]={'path':str(path),'free_bytes':free,'above_strict_floor':free>FLOOR,'device':os.stat(path).st_dev}
 return {'mode':'volatile-observation','filesystem':fs,'strict_free_bytes_floor':FLOOR,'process_scan':{'scanned':scanned,'inaccessible_or_disappeared':inaccessible,'exact_lean_lake_executable_or_argv0_matches':matches},
 'launch_authorized':False,'launch_supported':False,'atomic_reservation':False,'observation_is_not_build_authorization':True}
if __name__=='__main__':
 try:
  if sys.argv==[sys.argv[0],'--static']:result=static()
  elif sys.argv==[sys.argv[0],'--observe']:result=observe()
  else:raise ValueError('usage: preflight.py --static | --observe; no launch mode exists')
  print(json.dumps(result,indent=2,sort_keys=True))
 except Exception as e:
  print(json.dumps({'mode':'failure','launch_authorized':False,'launch_supported':False,'error_type':type(e).__name__,'error':str(e)},sort_keys=True))
  sys.exit(1)
