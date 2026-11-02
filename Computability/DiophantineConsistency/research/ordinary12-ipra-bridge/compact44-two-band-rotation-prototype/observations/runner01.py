#!/usr/bin/env python3
"""Single exploratory Lean check, all writable child paths on guarded tmpfs."""
import hashlib,json,os,pathlib,shutil,signal,subprocess,time
P=pathlib.Path; out=P('/dev/shm/ipra-two-band-explore-01');repo=P.cwd();src=repo/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-two-band-source-plan/TwoBand.lean';rot=P('/tmp/ipra-partial-band-rotation-01/CompactPartialBandRotation.olean');partial=P('/tmp/ipra-partial-band-rotation-01/lib/DiophantineConsistency/CompactPartialBand.olean');lean=P('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'); H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();pins={src:'a74bca80147584bbd0c22e593dfcef7bab827d6fafabe2cabf166c1688448d93',rot:'89dbf9c6d2fd44a986b6be7584be3973b02e9a83a3c100c54112ef0771dc3e67',partial:'0ac926e6c4ea770c88084922a1b65c6fa4df9b10f9faa57348db17b71cd00ae4',lean:'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'}
for p,h in pins.items():
 if not p.is_file() or H(p)!=h:raise RuntimeError(('pin drift',str(p)))
lib=P('/tmp/ipra-partial-band-rotation-01/lib/DiophantineConsistency');base=P('/tmp/ipra-compact-coefficient-decomposition-pair-01/author/lib/DiophantineConsistency')
for n in ('ArithmeticCyclicWord','CompactCoefficientDecoder'):
 p=lib/(n+'.olean');q=base/(n+'.olean')
 if not p.is_file() or p.resolve()!=q.resolve():raise RuntimeError(('provider mismatch',str(p)))
initial=shutil.disk_usage('/dev/shm').free
if initial<256*1024**2:raise RuntimeError(('tmpfs startup threshold',initial))
out.mkdir();(out/'lib/DiophantineConsistency').mkdir(parents=True);(out/'lib/DiophantineConsistency/CompactPartialBandRotation.olean').symlink_to(rot);shutil.copyfile(src,out/'TwoBand.lean')
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
