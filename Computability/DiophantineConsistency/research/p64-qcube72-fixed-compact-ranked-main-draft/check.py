#!/usr/bin/env python3
"""Single bounded Lean check; captured direct inputs, no provider rebuild."""
import hashlib,importlib.util,json,os,subprocess,sys,time
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('use python3 -I -S -B')
HERE=Path(__file__).resolve().parent;TASK=HERE.parents[1]
SOURCE=HERE/'FreeMainFixedCompactRankedMain.lean';LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OWNED=TASK/'research/current14-structured-endpoint-coherent-runner-v3/owned.py'
OUT=Path('/tmp/p64-qcube72-fixed-compact-ranked-main-check01')
DIRECT={
 'FreeMainSymbolicPortRankedMain':('/tmp/p64-qcube72-symbolic-port-ranked-main-priority-check03/FreeMainSymbolicPortRankedMain.olean','f5676747b761614f746b9dc6861c329b17f146520f229b6838b729a4d2fc009f'),
 'FreeMainActualRankWindowCompact':('/tmp/p64-qcube72-compact-port-opaque-check02/FreeMainActualRankWindowCompact.olean','f71306eaa4345a383e3721028a7c7e0aaf0b5d5276443792e9d2e787fbedd5b3'),
 'CompactSymbolicMaskData':('/tmp/p64-independent-captured-replay/lib/CompactSymbolicMaskData.olean','bce797f5b40fa75f130af592ed0c41e755f888ce9693538d1020cbd230004437'),
}
PATHS=['/tmp/p64-qcube72-symbolic-port-ranked-main-priority-check03', '/tmp/p64-qcube72-compact-port-opaque-check02', '/tmp/p64-qcube72-window-ranked-main-priority-check02', '/tmp/p64-qcube72-actual-rank-window-generic-check02', '/tmp/p64-qcube72-rank-half-priority-check02', '/tmp/p64-qcube72-ranked-main-priority-check03', '/tmp/p64-qcube72-conditional-rank-priority-check01', '/tmp/p64-qcube72-aux-norm-priority-check04', '/tmp/p64-qcube72-actual-large-priority-check02', '/tmp/p64-qcube72-main-root-priority-check01', '/tmp/p64-qcube72-main-index-lower-priority-check02', '/tmp/p64-qcube72-model-graph-divisibility-priority-check02', '/tmp/p64-qcube72-model-carrier-priority-check01', '/tmp/p64-qcube72-model-graph-shape-priority-check01', '/tmp/p64-qcube72-free-graph-priority-check01', '/tmp/p64-qcube72-model-divisibility-priority-check02', '/tmp/p64-qcube72-strong-norm-priority-check02', '/tmp/p64-qcube76y-strict-priority-check01', '/tmp/p64-qcube72-residuals-priority-check01', '/tmp/p64-qcube76y-size-priority-check06', '/tmp/p64-qcube76y-binding-priority-check01', '/tmp/p64-qcube76y-graph-model-priority-check02', '/tmp/p64-qcube76y-bounds-priority-check03', '/tmp/p64-qcube76y-priority-check04', '/tmp/p64-independent-captured-replay/lib', '/tmp', '/tmp/trace74-direct-four-block-1zltaw2f/lib', '/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib']
SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean','.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
PINS={SOURCE:'79eedcd56d95f2cc761609536bcf19c28119d2889806d0d3b480d573fa938159',LEAN:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',OWNED:'51f3ec69c2f4a11cfe118072f724a110c976a3557d1c68553ebb6a9c8108f498'}
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def guards():
 result={}
 for p,h in PINS.items():
  if not p.is_file() or sha(p)!=h:raise ValueError(('pin mismatch',str(p)))
  result[str(p)]={'realpath':str(p.resolve()),'sha256':h}
 for module,(path,h) in DIRECT.items():
  obj=Path(path)
  if not obj.is_file() or sha(obj)!=h:raise ValueError(('direct mismatch',module))
  root='/tmp/p64-independent-captured-replay/lib' if module.startswith('DiophantineConsistency/') else str(obj.parent)
  if root not in PATHS:raise ValueError(('missing root',module))
  for suffix in SUFFIXES:
   p=Path(path[:-6]+suffix)
   if os.path.lexists(p):
    if not p.is_file():raise ValueError(('bad companion',str(p)))
    result[str(p)]={'realpath':str(p.resolve()),'sha256':sha(p)}
   else:result[str(p)]=None
   for earlier in PATHS[:PATHS.index(root)]:
    sh=Path(earlier)/(module+suffix)
    if os.path.lexists(sh):raise ValueError(('direct shadow',str(sh)))
    result[str(sh)]=None
 return result
def available():
 for line in Path('/proc/meminfo').read_text().splitlines():
  if line.startswith('MemAvailable:'):return int(line.split()[1])*1024
 raise RuntimeError('MemAvailable unavailable')
def idle():
 ps=subprocess.run(['ps','-eo','stat=,comm='],check=True,text=True,stdout=subprocess.PIPE).stdout
 return not any(len(x)==2 and x[1]=='lean' and not x[0].startswith('Z') for x in (line.split() for line in ps.splitlines()))
if OUT.exists():raise SystemExit('refusing existing output')
before=guards();runner_sha=sha(__file__)
if available()<10*1024**3 or not idle():raise SystemExit('insufficient memory or Lean slot busy')
spec=importlib.util.spec_from_file_location('rank_owned',OWNED);owned=importlib.util.module_from_spec(spec);spec.loader.exec_module(owned)
OUT.mkdir();log=OUT/'compile.log';obj=OUT/'FreeMainFixedCompactRankedMain.olean';samples=[];start=time.monotonic();reason=None;code=None;receipt=None
env=dict(os.environ,LEAN_PATH=':'.join(PATHS),LEAN_NUM_THREADS='1')
for key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(key,None)
cmd=['ionice','-c3','nice','-n19',str(LEAN),'-M2400','-j1','-DElab.async=false','--root='+str(HERE),str(SOURCE),'-o',str(obj)]
def check(pid):
 rss=0;members=owned.group_live(pid)
 for member in members:
  try:rss+=int(Path('/proc',str(member),'statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
  except FileNotFoundError:pass
 mem=available();samples.append({'seconds':round(time.monotonic()-start,2),'rss_bytes':rss,'memavailable_bytes':mem,'members':members})
 return rss<7*1024**3//2 and mem>=10*1024**3
try:
 with log.open('x') as stream:code,seconds,receipt=owned.run(cmd,cwd=HERE,env=env,stdout=stream,stderr=subprocess.STDOUT,
                                                           timeout=120,disk_check=check,poll_interval=.25)
except BaseException as exc:reason=repr(exc);seconds=round(time.monotonic()-start,3)
try:
 after=guards();stable=before==after and sha(__file__)==runner_sha
except BaseException as exc:after={};stable=False;reason=repr(exc)
text=log.read_text() if log.exists() else ''
expected=['FreeMainFixedCompactRankedMain.fixed_main_at_rank']
import re
reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text,re.M|re.S)
allowed={'propext','Classical.choice','Quot.sound'}
passed=(code==0 and reason is None and bool(samples) and stable and obj.is_file() and not obj.is_symlink() and
        [n for n,_ in reports]==expected and all(not ({x.strip() for x in a.split(',') if x.strip()}-allowed) for _,a in reports) and
        not re.search(r'(?mi)^.*(?:error:|error\([^)]*\):|warning:)|\bsorryAx\b|\bsorry\b',text))
row={'status':'PASS' if passed else 'FAILED','exit':code,'failure':reason,'seconds':seconds,'command':cmd,'lean_path':PATHS,
     'samples':samples,'process_receipt':receipt,'guards_before':before,'guards_after':after,'guards_stable':stable,
     'source_sha256':sha(SOURCE),'runner_sha256':runner_sha,'log_sha256':sha(log) if log.exists() else None,
     'object_sha256':sha(obj) if obj.is_file() else None,'axiom_reports':reports,
     'scope':'One captured-provider check; direct input guards only, transitive/dynamic/between-sample ancestry inherited.'}
(OUT/'result.json').write_text(json.dumps(row,indent=2,sort_keys=True)+'\n');print(json.dumps(row,sort_keys=True),flush=True)
if not passed:raise SystemExit(1)
