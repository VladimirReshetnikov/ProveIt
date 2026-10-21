#!/usr/bin/env python3
"""Replay the independent FT shortcut certificate and bounded allocations.
Optional --runtime rederives all6152 arbitrary-natural cases on both tables.
Python3, NumPy, SciPy are needed; no network access or repository checkout.
"""
import argparse,json,subprocess,sys,hashlib
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
HERE=Path(__file__).resolve().parent

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--work',type=Path,required=True);ap.add_argument('--runtime',action='store_true');a=ap.parse_args();W=a.work.resolve();W.mkdir(parents=True,exist_ok=True);assert not any(W.iterdir()),'Use an empty output directory';assert W!=HERE and HERE not in W.parents
 def run(name,args):
  with (W/(name+'.log')).open('w')as log:subprocess.run([sys.executable,'-B',*map(str,args)],check=True,stdout=log,stderr=subprocess.STDOUT)
 run('local',[HERE/'ft_frontier.py','--output',W/'certificate'])
 new=json.loads((W/'certificate/result.json').read_text());old=json.loads((HERE/'ft-frontier/result.json').read_text())
 assert {k:v for k,v in new.items()if k!='seconds'}=={k:v for k,v in old.items()if k!='seconds'}
 run('startup',[HERE/'ft_startup.py','--new',W/'certificate/machine.native.tm','--output',W/'startup.json'])
 assert json.loads((W/'startup.json').read_text())==json.loads((HERE/'ft-frontier/startup-rows.json').read_text())
 if a.runtime:
  specs=[('baseline',HERE/'input3.tm','baseline-runtime.json'),('modified',W/'certificate/machine.native.tm','runtime.json')]
  with ThreadPoolExecutor(max_workers=2)as ex:
   fs=[ex.submit(run,name,[HERE/'ft_runtime_census.py','--table',table,'--output',W/out])for name,table,out in specs]
   for f in fs:f.result()
  for _,_,out in specs:
   got=json.loads((W/out).read_text());saved=json.loads((HERE/'ft-frontier'/out).read_text());assert {k:v for k,v in got.items()if k!='seconds'}=={k:v for k,v in saved.items()if k!='seconds'}
 results=[]
 for q in(-1,38,134):
  out=W/f'allocation-{q}';run(f'allocation-{q}',[HERE/'ft_allocate.py','--remove',q,'--seconds',25,'--output',out]);got=json.loads((out/'result.json').read_text());saved=json.loads((HERE/f'ft-frontier/allocation-{q}/result.json').read_text())
  for field in('status','nodes','protected_rows','variables','constraints','capacity_matching_size'):assert got[field]==saved[field]
  if q==-1:assert got['changed_rows']==[] and got['states']==215
  results.append({'remove':q,'status':got['status'],'capacity_matching_size':got['capacity_matching_size']})
 receipt={'status':'FT_FRONTIER_REPLAY_PASS','universal_runtime_rederived':a.runtime,'exact_local_joins':new['join_rows'],'invariant_contexts':new['invariant_contexts'],'states':215,'allocations':results,'scope':'Ordinary executable mathematical evidence. No214-state construction or formal kernel proof of the FT transformation.'};(W/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
