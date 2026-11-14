from pathlib import Path
import argparse,json,subprocess,sys,tempfile,shutil,hashlib
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--full',action='store_true');a=p.parse_args()
def run(name,cwd,opt=False):
 q=subprocess.run([sys.executable]+(['-O']if opt else[])+[name],cwd=cwd,capture_output=True,text=True)
 if q.returncode:raise RuntimeError(name+' failed: '+q.stdout+q.stderr)
 return q.stdout
r=[]
for opt in(False,True):
 for script in('check_windows.py','sanity.py'):
  run(script,ROOT,opt);r.append({'script':script,'optimized':opt,'status':'PASS'})
if a.full:
 with tempfile.TemporaryDirectory(prefix='boundary207-replay-') as d:
  work=Path(d)/'bundle';shutil.copytree(ROOT,work)
  # Parallel independent projection runs preserve each other's output identities.
  procs=[subprocess.Popen([sys.executable,s],cwd=work,stdout=subprocess.DEVNULL,stderr=subprocess.PIPE,text=True)for s in('project.py','project_specialized.py')]
  for s,q in zip(('project.py','project_specialized.py'),procs):
   _,err=q.communicate()
   if q.returncode:raise RuntimeError(s+' '+err)
   r.append({'script':s,'status':'PASS'})
  for script in('search.py','search_specialized.py','search_general.py'):
   run(script,work);r.append({'script':script,'status':'PASS'})
  for name in('windows.json','specialized_windows.json','search.json','specialized_search.json','general_search.json'):
   x=json.loads((ROOT/name).read_text());y=json.loads((work/name).read_text());x.pop('seconds',None);y.pop('seconds',None)
   if x!=y:raise ValueError('Fresh replay differs: '+name)
  r.append({'status':'ALL_FRESH_RECEIPTS_EQUAL_EXCEPT_TIMING'})
print(json.dumps({'status':'BOUNDARY_LANE_REPLAY_PASS','full_rederivation':a.full,'stages':r,'scope':'Ordinary symbolic/projection evidence; no accepted207construction.'},indent=2))
