#!/usr/bin/env python3
"""Compile the public facade/client using the freshly checked focused objects.
This appends no hypothesis and does not rebuild the full machine endpoint.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
ROOT=Path(__file__).resolve().parent
WORK=ROOT/'verification/work';LOGS=ROOT/'verification/logs'
flags=['-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
record={'scope':'Preserved K215F.Source215.p215_dagPerm interface and explicit typed client; not full endpoint','checks':[],'input_objects':{},'driver_sha256':sha(__file__)}
for p in WORK.rglob('*.vo'):record['input_objects'][str(p.relative_to(WORK))]=sha(p)
for name,rel in [('Source215','deps/K215F/Source215.v'),('EndpointClient','EndpointClient.v')]:
 src=ROOT/'integration'/(name+'.v');dst=WORK/rel;shutil.copyfile(src,dst)
 cmd=['coqc',*flags,rel];start=time.monotonic();log=LOGS/(name+'.log')
 with log.open('w') as stream:
  p=subprocess.Popen(cmd,cwd=WORK,stdout=stream,stderr=subprocess.STDOUT)
  _,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
 text=log.read_text();row={'name':name,'command':cmd,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3),'max_rss_kib':usage.ru_maxrss,'source_sha256':sha(src),'closed_reports':text.count('Closed under the global context'),'log_sha256':sha(log)}
 record['checks'].append(row);print(json.dumps(row),flush=True)
 if p.returncode or row['closed_reports']!=1 or 'Axioms:' in text:raise SystemExit(text)
record['complete']=True
(ROOT/'verification/interface-result.json').write_text(json.dumps(record,indent=2)+'\n')
