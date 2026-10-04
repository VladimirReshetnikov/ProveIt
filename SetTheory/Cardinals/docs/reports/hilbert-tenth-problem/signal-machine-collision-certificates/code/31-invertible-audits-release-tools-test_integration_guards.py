#!/usr/bin/env python3
import hashlib,json,os,shutil,subprocess
from pathlib import Path
A=Path('/workspace/shared/report61-release-tools-independent-review-20261004');seed=A/'final-source';out=A/'integration-guard-tests';out.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(r):return {p.relative_to(r).as_posix():{'sha256':sha(p),'mode':p.stat().st_mode,'mtime_ns':p.stat().st_mtime_ns} for p in r.rglob('*') if p.is_file()}
results=[]
for mode,expected in [('first-pass-input','Post-build dependency set differs'),('middle-png-corruption','Truncated PNG'),('missing-middle-page','Page render count mismatch'),('extra-page','Page render count mismatch')]:
 d=out/mode;d.mkdir();r=d/'release';shutil.copytree(seed,r);before=snap(r)
 args=['/usr/bin/python3','-I','-S','-B',str(A/'probe_build_guards.py'),mode,str(r/'tools/build_report61.py'),'--pins-sha',sha(r/'manuscript/MANUSCRIPT_PINS.json'),'--dependency-lock-sha',sha(r/'tools/BUILD_DEPENDENCIES_LOCK.json'),'--output-dir',str(d/'output')]
 p=subprocess.run(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8'},timeout=300)
 (d/'OUTPUT.log').write_bytes(p.stdout);same=before==snap(r)
 passed=p.returncode!=0 and expected.encode() in p.stdout and same and not (d/'output/BUILD_RECEIPT.json').exists()
 results.append({'mode':mode,'exit':p.returncode,'expected_error':expected,'source_unchanged':same,'pass':passed,'argv':args})
 if not passed:raise RuntimeError(p.stdout.decode(errors='replace'))
(out/'RESULTS.json').write_text(json.dumps(results,sort_keys=True,indent=2)+'\n');print(json.dumps({'status':'PASS','integration_cases':len(results),'instrumentation':'Controlled output-boundary mutation of inspected build tool; no scientific executables','results':results},indent=2))
