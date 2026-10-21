#!/usr/bin/env python3
"""Compile two new source modules against an already checked normalized closure."""
from pathlib import Path
import argparse,fcntl,hashlib,json,os,shutil,signal,subprocess,time
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--accepted-build',type=Path,required=True)
ap.add_argument('--out',type=Path,required=True)
a=ap.parse_args(); accepted=a.accepted_build.resolve();out=a.out.resolve()
if out.exists() and any(out.iterdir()):raise SystemExit('Use an empty output directory')
out.mkdir(parents=True,exist_ok=True);work=out/'work';work.mkdir();logs=out/'logs';logs.mkdir()
prior=json.loads((accepted/'result.json').read_text())
assert prior['status']=='PASS_COMPILED_SOURCE_EQUIVALENCE'
assert prior['recursive_source_check']=='passed'
compiler=shutil.which('coqc');assert compiler
assert sha(compiler)==prior['coqc_sha256']
base=accepted/'work'
flags=['-Q',str(base),'','-Q',str(base/'deps/K230'),'K230','-Q',str(base/'deps/K230P'),'K230P','-Q',str(base/'deps/K215F'),'K215F']
record={'scope':'Two newly compiled modules against ten exact reused providers; no fresh dependency rebuild or recursive check for this automatic instance.',
 'compiler':subprocess.check_output([compiler,'--version'],text=True).strip(),
 'compiler_sha256':sha(compiler),'accepted_receipt_sha256':sha(accepted/'result.json'),
 'inferred_entries_sha256':sha(root/'entries.json'),'build_driver_sha256':sha(root/'build.py'),
 'reused':[],'results':[]}
for b in prior['bindings']:
 if b['file'] in ['NormalizedCert215.v','Source215Normalized.v']:continue
 src=base/b['file'];obj=src.with_suffix('.vo')
 assert sha(src)==b['compiled_source_sha256']
 record['reused'].append({'module_file':b['file'],'source_sha256':sha(src),'object_sha256':sha(obj)})
for name in ['AutoCert215.v','Source215Auto.v']:
 shutil.copy2(root/name,work/name)
 cmd=[compiler,*flags,name];logfile=logs/(name+'.log')
 with Path('/tmp/proveit-k215-proof-build.lock').open('a') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX);start=time.monotonic()
  with logfile.open('w') as log:
   proc=subprocess.Popen(cmd,cwd=work,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
   try:code=proc.wait(timeout=180)
   except BaseException:
    os.killpg(proc.pid,signal.SIGKILL);proc.wait();raise
  elapsed=time.monotonic()-start
 text=logfile.read_text()
 result={'module':name,'source_sha256':sha(root/name),'argv':cmd,'exit_code':code,
 'elapsed_seconds':elapsed,'closed_reports':text.count('Closed under the global context'),
 'log_sha256':sha(logfile)}
 if code==0:result['object_sha256']=sha((work/name).with_suffix('.vo'))
 record['results'].append(result)
 (out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
 print(name,code,round(elapsed,3),text,flush=True)
 if code:raise SystemExit(code)
assert [x['closed_reports'] for x in record['results']]==[1,2]
record['status']='PASS_TWO_NEW_MODULES_WITH_BOUND_REUSED_CLOSURE'
record['recursive_check_for_new_instance']='not run'
(out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
