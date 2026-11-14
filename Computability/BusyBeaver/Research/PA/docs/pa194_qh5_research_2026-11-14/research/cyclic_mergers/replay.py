#!/usr/bin/env python3
"""Replay the bounded joint cyclic-merge search. Standard library + C++17."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse,hashlib,json,subprocess,time,tempfile
HERE=Path(__file__).resolve().parent

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);p.add_argument('--jobs',type=int,default=2);p.add_argument('--quick',action='store_true');a=p.parse_args()
 out=a.output or Path(tempfile.mkdtemp(prefix='pa-cyclic-merge-'))
 out.mkdir(parents=True,exist_ok=True)
 for name in ['cyclic_merge','cyclic_merge_terminal']:
  subprocess.run(['c++','-O3','-std=c++17',str(HERE/(name+'.cpp')),'-o',str(out/name)],check=True)
 for stem,engine,target in [('positive_control','cyclic_merge',3),('terminal_control','cyclic_merge_terminal',254)]:
  run=subprocess.run([str(out/engine),str(HERE/(stem+'.tm')),'2','20'],check=True,capture_output=True,text=True)
  rows=[json.loads(x)for x in run.stdout.splitlines()if x.strip()]
  assert {'remove':1,'keep':2,'actions':[[0,1,target],[1,1,target]]} in rows
 recorded=json.loads((HERE/'summary.json').read_text())
 for item in recorded['inputs']:
  assert digest(HERE/'inputs'/(item['class']+'.tm'))==item['input_sha256']
 assert all(x['working_target_solutions']==[] and x['terminal_target_solutions']==[] for x in recorded['inputs'])
 if a.quick:
  print(json.dumps({'positive_controls':'PASS','input_bindings':'PASS','negative_search_replayed':False,'output':str(out)},indent=2));return
 def job(item):
  cl=item['class'];table=HERE/'inputs'/(cl+'.tm');result={'class':cl,'input_sha256':digest(table)}
  for engine in ['cyclic_merge','cyclic_merge_terminal']:
   start=time.monotonic();run=subprocess.run([str(out/engine),str(table),'5','120'],check=True,capture_output=True,text=True)
   (out/(cl+'.'+engine+'.jsonl')).write_text(run.stdout)
   (out/(cl+'.'+engine+'.log')).write_text(run.stderr)
   lines=[json.loads(x)for x in run.stdout.splitlines()if x.strip()]
   assert not lines,(cl,engine,lines)
   assert 'DONE pairs=' in run.stderr
   result[engine]={'solutions':lines,'seconds':time.monotonic()-start,'last_line':run.stderr.splitlines()[-1]}
  return result
 with ThreadPoolExecutor(max_workers=max(1,a.jobs)) as pool:result=list(pool.map(job,recorded['inputs']))
 (out/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','negative_search_replayed':True,'tables':len(result),'accepted_mergers':0,'output':str(out)},indent=2))
if __name__=='__main__':main()
