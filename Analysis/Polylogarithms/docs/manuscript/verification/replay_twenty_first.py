"""Replay one preserved resonance package on an isolated copy.

Use the declared dependencies: mpmath 1.3.0, SymPy 1.14.0; parts 3/4
also require NumPy 2.3.5, and part 4 requires matplotlib 3.10.8.
The default fresh output is ignored; an existing destination is refused.
Original delivery files are never executed in place.
"""
from pathlib import Path
import argparse,json,os,shutil,subprocess,sys,tempfile,time
V=Path(__file__).resolve().parent;R=V.parents[4]
es=json.loads((V/'twenty-first-incoming-archives.json').read_text(encoding='utf-8'))
parser=argparse.ArgumentParser();parser.add_argument('part',type=int,choices=range(1,6));parser.add_argument('--output-directory',type=Path,default=V/'.scratch-twenty-first-replay');a=parser.parse_args();e=es[a.part-1]
root=Path(tempfile.mkdtemp(prefix='polylog-21-'+str(a.part)+'-'))/'package'
shutil.copytree((V.parent.parent/e['destination']).resolve(),root)
out=root/'fresh';out.mkdir();target=a.output_directory.resolve()/e['group'];target.mkdir(parents=True,exist_ok=False)
cmds={
1:[['verification/verify.py','--part','all','--output-dir','fresh'],['verification/verify_extensions.py','--output-dir','fresh']],
2:[['code/verify_exact.py'],['code/verify_numeric.py']],
3:[['code/verify.py','--output-dir','fresh'],['code/differentiation_pitfall.py']],
4:[['verification/coefficients.py','--output','fresh'],['verification/verify.py','--output','fresh']],
5:[['code/run_checks.py','--output-dir','fresh']]}[a.part]
env=os.environ.copy();env.update(PYTHONUTF8='1',PYTHONIOENCODING='utf-8',PYTHONOPTIMIZE='0',MPLBACKEND='Agg')
runs=[]
for i,cmd in enumerate(cmds,1):
 start=time.monotonic();log=target/(str(i)+'-'+Path(cmd[0]).stem+'.log')
 print(e['group'],cmd,'scratch',root,flush=True)
 with log.open('w',encoding='utf-8') as f: result=subprocess.run([sys.executable,'-X','utf8',*cmd],cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 runs.append(dict(command=cmd,exit_code=result.returncode,elapsed_seconds=round(time.monotonic()-start,3),log=log.name))
 print(e['group'],'exit',result.returncode,'seconds',runs[-1]['elapsed_seconds'],flush=True)
 if result.returncode:break
if a.part==2:
 for name in ['exact_checks.json','symbolic_coefficients.json','numeric_checks.json','numeric_table.tex']:
  p=root/'results'/name
  if p.exists():shutil.copyfile(p,out/name)
for p in out.rglob('*'):
 if p.is_file():
  q=target/'fresh'/p.relative_to(out);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
receipt=dict(group=e['group'],archive=e['archive'],source_pin=e['source_pin'],scratch=str(root),runs=runs,passed=len(runs)==len(cmds) and all(x['exit_code']==0 for x in runs),scope='Unmodified delivered mathematical programs run on an isolated copy, with assertions enabled and UTF-8 output. Finite exact checks and floating-point diagnostics do not certify all analytic proofs, interval enclosures or Lean formalization.')
(target/'replay-summary.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
print(json.dumps(receipt,indent=2),flush=True)
sys.exit(0 if receipt['passed'] else 1)
