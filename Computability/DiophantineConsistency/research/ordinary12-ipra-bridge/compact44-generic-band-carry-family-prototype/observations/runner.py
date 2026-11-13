#!/usr/bin/env python3
"""Bounded author-only direct-K/band K-cast exploration; not a paired replay."""
import hashlib,importlib.util,json,os,pathlib,re,shutil,signal,subprocess,sys,time
P=pathlib.Path;root=P.cwd();base=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge';plan=base/'compact44-direct-k-band-join-plan/scan.json';provider=P('/dev/shm/ipra-direct-k-band-explore-03');out=P('/dev/shm/ipra-kcast-explore-01');package=P('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib');monitor=base/'free-j-current-denominator-composition/replay.py';lean=P('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean');H=lambda p:hashlib.sha256(P(p).read_bytes()).hexdigest();START=256*1024**2;STOP=128*1024**2
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('isolated, nonoptimized Python required')
if H(plan)!='2048ee458a2f49755858e991e3837b71aab244ce9c8521e483e6cdea6282616d' or H(monitor)!='2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8' or H(lean)!='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550':raise RuntimeError('tool pin drift')
scan=json.loads(plan.read_bytes());progress=json.loads((provider/'progress.json').read_bytes());
if len(progress)!=14 or len(scan['source_order'])!=14:raise RuntimeError('provider incomplete')
def check_provider():
 for item,row in zip(progress,scan['source_order']):
  mod=row['module']; obj=(provider/'lib'/pathlib.Path(*mod.split('.'))).with_suffix('.olean');src=provider/'frozen/DiophantineConsistency'/(mod.split('.')[-1]+'.lean')
  if item['module']!=mod or item['compiler_exit']!=0 or item['stop_reason'] is not None or H(obj)!=item['object_sha256'] or H(src)!=row['source_sha256']:raise RuntimeError(('provider drift',mod))
 for name,expected in [('CompactSymbolicKernelOpaque','d3f437d06bac81de0214189bfda43ebfa76defba02e96e86afaf6546b581d90a'),('ArithmeticStandardCasts','c992bafb003c67229c756a634d31c11ecfb942839904367554488ba27ddc597a')]:
  if H(provider/'lib/DiophantineConsistency'/(name+'.olean'))!=expected:raise RuntimeError(('external pin drift',name))
check_provider()
for mod,sha in [('TwoBand','c6c08e4d92570aa4457cc72dd5f2c7d64aa429fdd9da4f26e871c99f063b0363'),('KCast','a62ebbbc42f35687d72abf31d98d7f2eb3d0217b77a2bdad9a11a809edce6fe0'),('SymbolicKBandDraft','90516e7b8ec94eb0f4b917979e0c2800c4e8b2c1c3362ea5131baa631415402f')]:
 if H(out/'lib/DiophantineConsistency'/(mod+'.olean'))!=sha:raise RuntimeError(('band/cast object drift',mod))
if sys.argv[1]=='init':
 if os.path.lexists(out) or shutil.disk_usage('/dev/shm').free<START:raise RuntimeError('output exists or startup tmpfs below 256 MiB')
 out.mkdir();sp=importlib.util.spec_from_file_location('monitor',monitor);m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m);m.overlay(provider/'lib',out/'lib');print(json.dumps({'status':'PREPARED_AUTHOR_ONLY_OVERLAY','provider':str(provider),'free_bytes':shutil.disk_usage('/dev/shm').free}),flush=True);sys.exit(0)
if len(sys.argv)!=5 or sys.argv[1]!='run':raise RuntimeError('run attempt module input')
attempt,mod,source=sys.argv[2:];source=P(source)
if not re.fullmatch(r'attempt[0-9]{2}',attempt) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*',mod) or not out.is_dir() or shutil.disk_usage('/dev/shm').free<START:raise RuntimeError('invalid run or low tmpfs')
srcsha=H(source);where=out/attempt;where.mkdir();frozen=where/'DiophantineConsistency';frozen.mkdir();src=frozen/(mod+'.lean');shutil.copyfile(source,src)
obj=(out/'lib/DiophantineConsistency'/(mod+'.olean')) if mod in ('TwoBand','FreeJGraphCongruenceExplore','CompactSymbolicGraphSaturation','CompactSameWitnessSaturation2','CompactDigitBound','CompactHeterogeneousCarry') else (where/(mod+'.olean'))
if os.path.lexists(obj):raise RuntimeError('object exists')
env=os.environ.copy()
for key in list(env):
 if key.startswith('PYTHON') or key in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(key,None)
env['TMPDIR']=str(out);env['LEAN_PATH']=str(out/'lib')+':'+str(package);cmd=[str(lean),'-M3000','-j1','-DElab.async=false','--root='+str(where),str(src),'-o',str(obj)];start=time.monotonic();minimum=shutil.disk_usage('/dev/shm').free;peak=0;count=0;reason=None
with (where/'compiler.log').open('xb') as f:
 p=subprocess.Popen(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 try:
  while p.poll() is None:
   free=shutil.disk_usage('/dev/shm').free;minimum=min(minimum,free)
   try:
    lines=(P('/proc')/str(p.pid)/'status').read_text().splitlines();rss=next(int(x.split()[1])*1024 for x in lines if x.startswith('VmRSS:'));peak=max(peak,rss);count+=1
   except (OSError,StopIteration):
    deadline=time.monotonic()+1
    while p.poll() is None and time.monotonic()<deadline:
     time.sleep(.05)
     try:
      lines=(P('/proc')/str(p.pid)/'status').read_text().splitlines();rss=next(int(x.split()[1])*1024 for x in lines if x.startswith('VmRSS:'));peak=max(peak,rss);count+=1;break
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
minimum=min(minimum,shutil.disk_usage('/dev/shm').free);check_provider();drift=H(source)!=srcsha or H(src)!=srcsha;log=where/'compiler.log';receipt={'attempt':attempt,'module':mod,'source_sha256':srcsha,'compiler_exit':code,'stop_reason':reason,'sampled_peak_rss_bytes':peak,'rss_samples':count,'sampled_min_tmpfs_free_bytes':minimum,'elapsed_seconds':round(time.monotonic()-start,3),'log_sha256':H(log),'object_sha256':H(obj) if obj.is_file() else None,'source_drift':drift,'provider':'/dev/shm/ipra-direct-k-band-explore-03/lib','command':cmd,'scope':'Author-only exploratory check; no guarded pair, retained-byte binding or internal PRA theorem.'};(where/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt,sort_keys=True),flush=True)
