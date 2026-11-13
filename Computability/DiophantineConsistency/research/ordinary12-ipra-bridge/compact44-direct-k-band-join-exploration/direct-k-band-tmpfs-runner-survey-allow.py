#!/usr/bin/env python3
"""Author-only exploratory coherent suffix with sampled tmpfs/RSS checks."""
import hashlib,importlib.util,json,os,re,shutil,signal,subprocess,sys,time
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs');BASE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';PLAN=BASE/'compact44-direct-k-band-join-plan';PROVIDER=Path('/tmp/ipra-direct-symbolic-k-pair-01/author/lib');PACKAGE=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');OUT=Path('/dev/shm/ipra-direct-k-band-explore-03');LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');MONITOR=BASE/'free-j-current-denominator-composition/replay.py';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();START=256*1024**2;STOP=128*1024**2
assert H(PLAN/'scan.json')=='2048ee458a2f49755858e991e3837b71aab244ce9c8521e483e6cdea6282616d' and H(LEAN)=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550' and H(MONITOR)=='2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8'
scan=json.loads((PLAN/'scan.json').read_bytes());assert scan['status']=='PRELIMINARY_DIRECT_K_PARTIAL_BAND_JOIN_NOT_A_BUILD' and len(scan['source_order'])==14
assert not os.path.lexists(OUT) and shutil.disk_usage('/dev/shm').free>=START
for row in scan['source_order']:
 p=Path(row['source']);assert p.is_file() and H(p)==row['source_sha256']
for row in scan['parent_objects']['author']:
 p=PROVIDER/row['path'];assert p.is_file() and str(p.resolve())==row['realpath'] and H(p)==row['sha256']
for name,item in {**scan['external_direct_slots'],**scan['package_slots']}.items():
 if '/peer/' in name:continue
 p=Path(name)
 if item is None:assert not os.path.lexists(p),name
 else:assert p.is_file() and str(p.resolve())==item['realpath'] and H(p)==item['sha256'],name
sp=importlib.util.spec_from_file_location('monitor',MONITOR);monitor=importlib.util.module_from_spec(sp);sp.loader.exec_module(monitor);OUT.mkdir();LIB=OUT/'lib';monitor.overlay(PROVIDER,LIB);FROZEN=OUT/'frozen/DiophantineConsistency';FROZEN.mkdir(parents=True)
for row in scan['source_order']:
 dst=FROZEN/(row['module'].split('.')[-1]+'.lean');shutil.copyfile(row['source'],dst);assert H(dst)==row['source_sha256']
assert shutil.disk_usage('/dev/shm').free>=START
ENV=os.environ.copy()
for k in list(ENV):
 if k.startswith('PYTHON') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):ENV.pop(k,None)
ENV['TMPDIR']=str(OUT);ENV['LEAN_PATH']=str(LIB)+':'+str(PACKAGE)
progress=[];minimum=shutil.disk_usage('/dev/shm').free

def monitored(cmd,log):
 global minimum
 start=time.monotonic();peak=0;count=0;reason=None
 with log.open('xb') as f:
  p=subprocess.Popen(cmd,env=ENV,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
  try:
   while p.poll() is None:
    free=shutil.disk_usage('/dev/shm').free;minimum=min(minimum,free)
    try:
     lines=(Path('/proc')/str(p.pid)/'status').read_text().splitlines();rss=next(int(x.split()[1])*1024 for x in lines if x.startswith('VmRSS:'));peak=max(peak,rss);count+=1
    except (OSError,StopIteration):
     deadline=time.monotonic()+1
     while p.poll() is None and time.monotonic()<deadline:
      time.sleep(.05)
      try:
       lines=(Path('/proc')/str(p.pid)/'status').read_text().splitlines();rss=next(int(x.split()[1])*1024 for x in lines if x.startswith('VmRSS:'));peak=max(peak,rss);count+=1;break
      except (OSError,StopIteration):pass
     else:
      if p.poll() is None:reason='rss_unavailable'
     if reason or p.poll() is not None:break
    if free<STOP:reason='tmpfs_free_below_128MiB';break
    if peak>int(3.5*1024**3):reason='rss_above_3.5GiB';break
    if time.monotonic()-start>120:reason='timeout_120s';break
    time.sleep(.2)
   if reason:
    try:os.killpg(p.pid,signal.SIGTERM)
    except ProcessLookupError:pass
    try:p.wait(timeout=5)
    except subprocess.TimeoutExpired:
     try:os.killpg(p.pid,signal.SIGKILL)
     except ProcessLookupError:pass
     p.wait(timeout=5)
   code=p.wait(timeout=5)
  finally:
   if p.poll() is None:
    try:os.killpg(p.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    p.wait(timeout=5)
 minimum=min(minimum,shutil.disk_usage('/dev/shm').free)
 return code,peak,count,reason
for row in scan['source_order']:
 name=row['module'];src=FROZEN/(name.split('.')[-1]+'.lean');obj=(LIB/Path(*name.split('.'))).with_suffix('.olean');assert H(src)==row['source_sha256'] and H(row['source'])==row['source_sha256'] and not os.path.lexists(obj)
 expected={str(PACKAGE/'Init.olean')}
 for dep in row['imports']:
  path=(LIB if dep.startswith('DiophantineConsistency.') else PACKAGE)/Path(*dep.split('.'));p=path.with_suffix('.olean');assert p.is_file(),('missing import',name,str(p));expected.add(str(p))
 q=subprocess.run([str(LEAN),'--deps',str(src)],env=ENV,capture_output=True,text=True,timeout=60);assert q.returncode==0 and not q.stderr and set(q.stdout.splitlines())==expected,('deps',name,q.returncode,q.stdout,q.stderr)
 cmd=[str(LEAN),'-M3000','-j1','-DElab.async=false','--root='+str(OUT/'frozen'),str(src),'-o',str(obj)];log=OUT/(name.split('.')[-1]+'.log');code,peak,count,reason=monitored(cmd,log);text=log.read_text();record={'module':name,'compiler_exit':code,'stop_reason':reason,'sampled_peak_rss_bytes':peak,'rss_samples':count,'sampled_min_tmpfs_free_bytes':minimum,'source_sha256':H(src),'deps_stdout':q.stdout,'log_sha256':H(log),'object_sha256':H(obj) if obj.is_file() else None};progress.append(record);(OUT/'progress.json').write_text(json.dumps(progress,indent=2)+'\n');print(json.dumps(record),flush=True)
 reports=re.findall(r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$",text,re.M);expected_reports=row['axiom_reports']
 allowed=''
 warning_mismatch=False
 survey=Path('/tmp/direct-k-band-warning-survey.json')
 assert H(survey)=='52aaf3f727e9269bead5c35f29b60f003c7aaed282b0f288ccf70760a8be3f4f'
 entry=next(x for x in json.loads(survey.read_bytes())['entries'] if x['module']==name.split('.')[-1])
 assert entry['source_sha256']==row['source_sha256']
 if entry['warning_suffixes']:
  assert len(entry['warning_suffixes'])==1
  expected_warning=str(src)+entry['warning_suffixes'][0]
  if text==expected_warning:allowed=expected_warning
  else:warning_mismatch=True
 if warning_mismatch or code!=0 or reason is not None or not obj.is_file() or obj.is_symlink() or H(src)!=row['source_sha256'] or H(row['source'])!=row['source_sha256'] or re.search(r'(?m)^.*(?:error:|warning:)|\bsorryAx\b|\bsorry\b',text.removeprefix(allowed)) or [x[0] for x in reports]!=expected_reports:
  raise RuntimeError(('failed child or report',name,code,reason,text[-5000:]))
for row in scan['source_order']:assert H(FROZEN/(row['module'].split('.')[-1]+'.lean'))==row['source_sha256'] and H(row['source'])==row['source_sha256']
print(json.dumps({'status':'PASS_AUTHOR_ONLY_DIRECT_K_PARTIAL_BAND_TMPFS','children':len(progress),'sampled_min_tmpfs_free_bytes':minimum,'scope':'Exploratory author-only source rebuild; no guarded pair, model K cast, retained bytes, full column, fractional temporal or iPRA proof.'}),flush=True)
