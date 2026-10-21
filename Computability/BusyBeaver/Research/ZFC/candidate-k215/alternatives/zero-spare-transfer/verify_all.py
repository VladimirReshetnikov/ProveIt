#!/usr/bin/env python3
"""Owned offline orchestrator for the exact zero-spare215 research packet."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time
from concurrent.futures import ThreadPoolExecutor
R=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE'): raise RuntimeError('Assertions must be enabled')
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--runtime',action='store_true');ap.add_argument('--state35',action='store_true');ap.add_argument('--synthesis',action='store_true');ap.add_argument('--jobs',type=int,default=1);a=ap.parse_args()
 assert 1<=a.jobs<=8
 assert not a.synthesis or a.state35,'--synthesis requires --state35'
 m=json.loads((R/'MANIFEST.json').read_text());seen=set()
 for x in m['files']:
  rel=Path(x['path']);assert not rel.is_absolute() and '..' not in rel.parts
  p=R/rel;assert p.is_file() and not p.is_symlink() and p.stat().st_size==x['bytes'] and H(p)==x['sha256'],str(rel)
  assert str(rel) not in seen;seen.add(str(rel))
 actual={str(p.relative_to(R))for p in R.rglob('*')if p.is_file() and '__pycache__'not in p.parts and p.suffix!='.pyc'}
 assert actual==seen|{'MANIFEST.json'},actual.symmetric_difference(seen|{'MANIFEST.json'})
 W=a.work.resolve();assert not W.is_relative_to(R),'Choose a work directory outside the packet';W.mkdir(parents=True,exist_ok=False);start=time.monotonic();results=[]
 env=dict(os.environ);env.pop('PYTHONPATH',None);env.pop('PYTHONHOME',None);env['PYTHONDONTWRITEBYTECODE']='1'
 def run(label,script,extra):
  cmd=[sys.executable,'-I','-B',str(R/script),*extra];log=W/(label+'.log')
  print('Running',label,flush=True)
  with log.open('w')as f:subprocess.run(cmd,cwd=W,env=env,stdout=f,stderr=subprocess.STDOUT,check=True)
  results.append({'name':label,'status':'PASS','log_sha256':H(log)})
 tasks=[]
 for name in ['primary','mp0_216','secondary_association','optional_reparse']:
  tasks.append((name,name+'/verify.py',(['--runtime']if a.runtime else[])+['--work',str(W/(name+'-output'))]))
 for name,script in [('prefix','check_prefix_encoding.py'),('constructor','check_constructor_mismatch.py'),('graphs','check_graph_distinction.py')]:
  tasks.append((name,'supplement/checks/'+script,['--work',str(W/(name+'-output'))]))
 if a.state35:tasks.append(('state35','supplement/checks/check_state35_left_bound.py',['--work',str(W/'state35-output')]))
 with ThreadPoolExecutor(max_workers=a.jobs)as pool:
  futures=[pool.submit(run,*task)for task in tasks]
  for f in futures:f.result()
 if a.synthesis:
  cc=shutil.which('c++')or shutil.which('g++');assert cc,'C++17 compiler required only for --synthesis'
  exe=W/'state35-search';subprocess.run([cc,'-std=c++17','-O2',str(R/'supplement/checks/synthesize_state35.cpp'),'-o',str(exe)],cwd=W,env=env,check=True)
  log=W/'state35-synthesis.log'
  with log.open('w')as f:subprocess.run([str(exe),str(R/'supplement/negative_controls/rejected_old_delete301_214.native.tm'),str(W/'state35-output/state35_replay_windows19.txt')],cwd=W,env=env,stdout=f,check=True)
  assert H(log)=='5000d900c9082949fb16fef9ecb7413af240de39ea6c6121b75a7fcfe9a7b0db'
  results.append({'name':'state35-synthesis','status':'PASS','log_sha256':H(log)})
 for x in m['files']:assert H(R/x['path'])==x['sha256'],'Input changed during replay: '+x['path']
 out={'status':'RELEASE_REPLAY_PASS','runtime':a.runtime,'state35':a.state35,'synthesis':a.synthesis,'manifest_sha256':H(R/'MANIFEST.json'),'results':sorted(results,key=lambda x:x['name']),'seconds':time.monotonic()-start,'scope':'Owned finite/symbolic checkers; ordinary mathematical compiler/calibration proofs remain separate. No new proof-assistant endpoint.'}
 (W/'RELEASE_REPLAY.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
