#!/usr/bin/env python3
"""Replay the pinned finite contraction screens; no repository or network needed."""
from pathlib import Path
import argparse,hashlib,json,subprocess,tempfile,time
from concurrent.futures import ThreadPoolExecutor,as_completed
HERE=Path(__file__).resolve().parent

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--workers',type=int,default=2);ap.add_argument('--group',action='append');ap.add_argument('--quick',action='store_true');ap.add_argument('--output',type=Path,default=None);args=ap.parse_args()
 if args.output is None:args.output=HERE/'receipts'/('quick_fresh.json' if args.quick else 'replay_fresh.json')
 manifest=json.loads((HERE/'manifest.json').read_text())
 for name,sha in manifest['files'].items():
  if digest(HERE/name)!=sha:raise SystemExit('Input hash mismatch: '+name)
 cases=[c for c in manifest['cases']if not args.group or c['group']in args.group]
 result={'status':'running','source_commit':manifest['commit'],'case_count':len(cases),'groups':sorted({c['group']for c in cases}),'code_sha256':{p.name:digest(p)for p in(HERE/'code').glob('*.cpp')},'fixtures':{},'cases':[]}
 with tempfile.TemporaryDirectory(prefix='conpa_contractions_')as td:
  td=Path(td)
  for source in (HERE/'code').glob('*.cpp'):
   subprocess.run(['c++','-O3','-std=c++17',str(source),'-o',str(td/source.stem)],check=True,capture_output=True)
  for op,inp,expected in [('shift_merge','shift.tm','SHIFT 1 -> 2 offset -2'),('retag_merge','retag.tm','RETAG 1 -> 2 offset 0 mark -1'),('retag_actions','retag.tm','RETAG-ACTION 1 -> 2 offset 0 mark -1')]:
   v=subprocess.run([str(td/op),str(HERE/'fixtures'/inp),'5','20'],check=True,capture_output=True,text=True)
   if expected not in v.stdout:raise RuntimeError('Positive fixture was not recognized: '+op)
   result['fixtures'][op]={'pass':True,'expected_witness':expected,'stdout_sha256':hashlib.sha256(v.stdout.encode()).hexdigest()}
  def run(c):
   command=[str(td/c['operator']),str(HERE/c['table']),str(c['radius']),str(c['steps'])]
   if 'patterns'in c:command.append(str(HERE/c['patterns']))
   started=time.monotonic();v=subprocess.run(command,capture_output=True,text=True)
   return {'case_id':c['case_id'],'pass':v.returncode==0 and v.stdout==c['expected_stdout'],'returncode':v.returncode,'stdout':v.stdout,'elapsed_seconds':round(time.monotonic()-started,3)}
  if not args.quick:
   with ThreadPoolExecutor(max_workers=args.workers)as pool:
    future={pool.submit(run,c):i for i,c in enumerate(cases)};ordered={}
    for f in as_completed(future):
     r=f.result();ordered[future[f]]=r
     if not r['pass']:print('UNEXPECTED RESULT',r,flush=True)
     if len(ordered)%20==0:print('completed',len(ordered),'of',len(cases),flush=True)
    result['cases']=[ordered[i]for i in range(len(cases))]
 result['status']='fixtures_only_passed'if args.quick else'passed'if all(r['pass']for r in result['cases'])else'unexpected_result'
 args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(result['status'],len(result['cases']),'screens; output',args.output,flush=True)
 if result['status']=='unexpected_result':raise SystemExit(1)
if __name__=='__main__':main()
