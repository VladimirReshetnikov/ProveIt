#!/usr/bin/env python3
"""Single exploratory Lean check, all writable child paths on guarded tmpfs."""
import hashlib,importlib.util,json,os,pathlib,shutil,signal,subprocess,time
P=pathlib.Path; out=P('/dev/shm/ipra-two-band-explore-03');repo=P.cwd();src=P('/tmp/TwoBand-helper.lean');rot=P('/tmp/ipra-partial-band-rotation-01/CompactPartialBandRotation.olean');partial=P('/tmp/ipra-partial-band-rotation-01/lib/DiophantineConsistency/CompactPartialBand.olean');lean=P('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'); H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pins={src:'6bf2dc0cf02bc32ccff07cc5cc3b66f271fc86bed01dfc151a07f39893a48908',rot:'89dbf9c6d2fd44a986b6be7584be3973b02e9a83a3c100c54112ef0771dc3e67',partial:'0ac926e6c4ea770c88084922a1b65c6fa4df9b10f9faa57348db17b71cd00ae4',lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
for p,h in pins.items():
 if not p.is_file() or H(p)!=h:raise RuntimeError(('pin drift',str(p)))
lib=P('/tmp/ipra-partial-band-rotation-01/lib/DiophantineConsistency');base=P('/tmp/ipra-compact-coefficient-decomposition-pair-01/author/lib/DiophantineConsistency')
for n in ('ArithmeticCyclicWord','CompactCoefficientDecoder'):
 p=lib/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or p.resolve()!=q.resolve():raise RuntimeError(('provider mismatch',str(p)))
initial=shutil.disk_usage('/dev/shm').free
if initial<256*1024**2:raise RuntimeError(('tmpfs startup threshold',initial))
out.mkdir();monitor=repo/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py'
if H(monitor)!='2c8a7f848e715a297f8af31e6a2be46747db0d571bc9fa1f104ab06d2db94eb8':raise RuntimeError('overlay helper drift')
spec=importlib.util.spec_from_file_location('monitor',monitor);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.overlay(P('/tmp/ipra-partial-band-rotation-01/lib'),out/'lib');(out/'lib/DiophantineConsistency/CompactPartialBandRotation.olean').symlink_to(rot);shutil.copyfile(src,out/'TwoBand.lean')
if shutil.disk_usage('/dev/shm').free<256*1024**2:raise RuntimeError('tmpfs threshold after overlay')
env=os.environ.copy()
for k in list(env):
 if k.startswith('PYTHON') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(k,None)
env['TMPDIR']=str(out);env['LEAN_PATH']=str(out/'lib')+':/tmp/ipra-partial-band-rotation-01/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
cmd=[str(lean),'-M3000','-j1','-DElab.async=false','--root='+str(out),str(out/'TwoBand.lean'),'-o',str(out/'TwoBand.olean')];start=time.monotonic();minimum=initial;peak=0;count=0;reason=None
with (out/'compiler.log').open('xb') as f:
 p=subprocess.Popen(cmd,env=env,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 try:
  while p.poll() is None:
   free=shutil.disk_usage('/dev/shm').free;minimum=min(minimum,free)
   try:
    status=P('/proc')/str(p.pid)/'status';lines=status.read_text().splitlines();rss=next(int(x.split()[1])*1024 for x in lines if x.startswith('VmRSS:'));peak=max(peak,rss);count+=1
   except (OSError,StopIteration):
    if p.poll() is None:reason='rss_unavailable';break
   if free<128*1024**2:reason='tmpfs_free_below_128MiB';break
   if peak>int(3.5*1024**3):reason='rss_above_3.5GiB';break
   if time.monotonic()-start>120:reason='timeout_120s';break
   time.sleep(0.2)
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
end=shutil.disk_usage('/dev/shm').free;minimum=min(minimum,end);drift=[str(p) for p,h in pins.items() if not p.is_file() or H(p)!=h];receipt={'status':'EXPLORATORY_SINGLE_AUTHOR_ONLY','command':cmd,'source_sha256':H(out/'TwoBand.lean'),'compiler_exit':code,'stop_reason':reason,'samples':count,'peak_rss_bytes':peak,'tmpfs_initial_bytes':initial,'tmpfs_minimum_bytes':minimum,'tmpfs_final_bytes':end,'tmpfs_stop_threshold_bytes':128*1024**2,'elapsed_seconds':round(time.monotonic()-start,3),'compiler_log_sha256':H(out/'compiler.log'),'output_sha256':H(out/'TwoBand.olean') if (out/'TwoBand.olean').is_file() else None,'pin_drift':drift,'provider':'/tmp/ipra-compact-coefficient-decomposition-pair-01/author/lib through exploratory band rotation overlay','scope':'Unpaired exploratory author-side check only; not a guarded replay, provider re-audit or internal PRA theorem.'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt,sort_keys=True),flush=True)
