#!/usr/bin/env python3
"""Serial, memory-capped kernel compilation of the independent CM215 bridge."""
from pathlib import Path
import argparse,subprocess,os,time,json,resource,hashlib

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--lean',required=True)
 p.add_argument('--source',type=Path,default=Path(__file__).resolve().parent/'lean')
 p.add_argument('--memory-mb',type=int,default=768)
 p.add_argument('--timeout',type=int,default=180)
 a=p.parse_args();src=a.source.resolve(); logs=src/'logs';logs.mkdir(exist_ok=True)
 env=dict(os.environ,LEAN_PATH=str(src))
 modules=['PositiveStuttering','MarkerTransport','FiniteMarkerCertificate','CM215Tables']+[x.stem for x in sorted(src.glob('CM215Check*.lean'))]+['CM215Certificate']
 result={'status':'RUNNING','lean_version':subprocess.run([a.lean,'--version'],capture_output=True,text=True,check=True).stdout.strip(),'modules':[]}
 for m in modules:
  path=src/(m+'.lean');start=time.monotonic()
  with (logs/(m+'.log')).open('w') as f:
   pr=subprocess.run([a.lean,'-M',str(a.memory_mb),'-o',m+'.olean',m+'.lean'],cwd=src,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=a.timeout)
  log=(logs/(m+'.log')).read_text()
  record={'module':m,'returncode':pr.returncode,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.encode()).hexdigest()}
  result['modules'].append(record)
  print(json.dumps(record),flush=True)
  if pr.returncode or 'sorryAx' in log or 'error:' in log:
   result['status']='FAIL';print(log);break
 else:result['status']='PASS'
 result['max_child_rss_kib']=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
 if (logs/'CM215Certificate.log').exists():result['endpoint_axiom_report']=(logs/'CM215Certificate.log').read_text()
 (src/'kernel_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 if result['status']!='PASS':raise SystemExit(1)
 print(json.dumps({'status':result['status'],'max_child_rss_kib':result['max_child_rss_kib']}))
if __name__=='__main__': main()
