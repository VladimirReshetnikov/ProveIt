#!/usr/bin/env python3
"""Compile and independently kernel-check the generic positive-block theorem."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,time

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

ap=argparse.ArgumentParser();ap.add_argument('--coqc',default=shutil.which('coqc'))
ap.add_argument('--coqchk',default=shutil.which('coqchk'));ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args();assert a.coqc and a.coqchk,'Pass --coqc and --coqchk or put them on PATH.'
src=Path(__file__).with_name('PositiveTransport.v');out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
copy=out/src.name;assert copy!=src.resolve(),'Choose a separate proof-output directory.';shutil.copyfile(src,copy)
started=time.monotonic();version=subprocess.check_output([a.coqc,'--version'],text=True).strip()
compile_=subprocess.run([a.coqc,'-Q',str(out),'',str(copy)],capture_output=True,text=True)
(out/'coqc.log').write_text(compile_.stdout+compile_.stderr)
result=dict(status='FAILED',compiler=version,source_sha256=digest(src),compile_exit=compile_.returncode,
 scope='Generic deterministic positive-block halting/nonhalting transport only. No exact table or ZFC theory endpoint is instantiated.')
if compile_.returncode==0:
 assert compile_.stdout.count('Closed under the global context')==2,'Assumption audit failed.'
 check=subprocess.run([a.coqchk,'-Q',str(out),'','-silent','-o','PositiveTransport'],capture_output=True,text=True)
 (out/'coqchk.log').write_text(check.stdout+check.stderr)
 result.update(kernel_exit=check.returncode,kernel_log_sha256=digest(out/'coqchk.log'),closed_reports=2)
 if check.returncode==0:result['status']='ROCQ_GENERIC_TRANSPORT_CHECK_PASS'
result.update(seconds=time.monotonic()-started,compile_log_sha256=digest(out/'coqc.log'))
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
assert result['status']=='ROCQ_GENERIC_TRANSPORT_CHECK_PASS'
