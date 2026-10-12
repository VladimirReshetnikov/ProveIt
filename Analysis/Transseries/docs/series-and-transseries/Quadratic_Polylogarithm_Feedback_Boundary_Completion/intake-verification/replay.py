"""Replay all five delivered suites in an isolated working copy."""
from pathlib import Path
import sys,os,json,subprocess,time,argparse,tempfile,shutil
from concurrent.futures import ThreadPoolExecutor,as_completed
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-directory',type=Path,required=True)
args=parser.parse_args()
out=args.output_directory.resolve()
assert not out.exists(), 'Choose a new output directory to preserve recorded evidence.'
source=Path(__file__).resolve().parents[1]
root=Path(tempfile.mkdtemp(prefix='polylog-feedback-replay-'))/'package'
shutil.copytree(source,root,ignore=shutil.ignore_patterns('intake-verification','__pycache__'))

out.mkdir(exist_ok=False)
jobs=['feedback_verify','verify_coefficient_crossover','verify_critical_charts','verify_crossover','verify_joint_crossover']
def run(name):
 target=out/name;target.mkdir()
 cmd=[sys.executable,str(root/'code'/f'{name}.py'),'--output-dir',str(target)]
 if name=='verify_joint_crossover':cmd+=['--X','40','80','--dps','180']
 start=time.monotonic()
 with (target/'run.log').open('w',encoding='utf-8') as log:
  result=subprocess.run(cmd,cwd=root,stdout=log,stderr=subprocess.STDOUT)
 return dict(suite=name,command=cmd,exit_code=result.returncode,elapsed_seconds=round(time.monotonic()-start,3))
rows=[]
with ThreadPoolExecutor(max_workers=3) as pool:
 for f in as_completed([pool.submit(run,n) for n in jobs]):
  row=f.result();rows.append(row)
  print(row['suite'],row['exit_code'],row['elapsed_seconds'],flush=True)
result=dict(suites=sorted(rows,key=lambda r:r['suite']),python=sys.version,originals_executed_in_place=False,all_processes_succeeded=all(r['exit_code']==0 for r in rows),scope='Fresh full default grids; process success and emitted checks are distinct from proof or interval certification.')
(out/'runner.json').write_text(json.dumps(result,indent=2)+'\n')
assert result['all_processes_succeeded']
