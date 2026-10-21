#!/usr/bin/env python3
"""Three explicitly selected Source158 leaves; no manifest/wrapper/search/runtime."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, time
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 src=a.packet.resolve();out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
 p=out/'packet';shutil.copytree(src,p);logs=out/'logs';logs.mkdir();dest=out/'results';dest.mkdir()
 jobs=[('seed3',['code/replay_seed3.py','--check-only','data/seed3-proof.json','--output',str(dest/'seed3')],['code/replay_seed3.py','data/seed3-proof.json']),('action-variants',['code/verify_action_variants.py','data/k218.native.tm','data/action-variants.txt','--output',str(dest/'action-variants.json')],['code/verify_action_variants.py','data/k218.native.tm','data/action-variants.txt']),('scanner-route',['code/verify_scanner_route.py','--accepted','data/k218.native.tm','--short','data/delete50.native.tm','--sites','data/sites218.json','--output',str(dest/'scanner-route.json')],['code/verify_scanner_route.py','data/k218.native.tm','data/delete50.native.tm','data/sites218.json'])]
 files=sorted(set(f for _,_,fs in jobs for f in fs));before={f:sha(p/f)for f in files}
 rec={'status':'RUNNING','source_packet':str(src),'disposable_packet':str(p),'scope':'Only three authorized standalone leaves. No wrapper, manifest, ancestor, core runtime, search, compiler or proof assistant.','wall_cap_seconds_each':60,'inputs_before':before,'jobs':[],'runner_sha256':sha(Path(__file__))}
 env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
 for name,args,_ in jobs:
  argv=[sys.executable,'-B',*args];start=time.monotonic();timeout=False
  with (logs/(name+'.stdout')).open('wb') as so,(logs/(name+'.stderr')).open('wb') as se:
   try:r=subprocess.run(argv,cwd=p,env=env,stdout=so,stderr=se,timeout=60);rc=r.returncode
   except subprocess.TimeoutExpired:timeout=True;rc=None
  item={'name':name,'argv':argv,'cwd':str(p),'returncode':rc,'timeout':timeout,'seconds':time.monotonic()-start,'stdout':str(logs/(name+'.stdout')),'stderr':str(logs/(name+'.stderr')),'stdout_sha256':sha(logs/(name+'.stdout')),'stderr_sha256':sha(logs/(name+'.stderr'))}
  rec['jobs'].append(item);(out/'actual.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(item),flush=True)
  if rc!=0 or timeout:break
 rec['inputs_after']={f:sha(p/f)for f in files};rec['inputs_unchanged']=before==rec['inputs_after']
 rec['outputs']=[{'path':str(f.relative_to(out)),'bytes':f.stat().st_size,'sha256':sha(f)}for f in sorted(dest.rglob('*'))if f.is_file()]
 rec['status']='SELECTED_LEAVES_PASS' if len(rec['jobs'])==3 and all(j['returncode']==0 and not j['timeout']for j in rec['jobs'])and rec['inputs_unchanged'] else 'SELECTED_LEAVES_INCOMPLETE_OR_FAILED'
 (out/'actual.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],flush=True)
if __name__=='__main__':main()
