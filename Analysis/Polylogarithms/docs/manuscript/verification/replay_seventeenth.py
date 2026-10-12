"""Full mathematical suites for the seventeenth intake, only on isolated copies.

Package-manifest programs and document rebuilds are deliberately outside
these mathematical replay commands; delivered files remain unchanged.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
B=Path(__file__).resolve().parents[1];V=B/'verification'
plans={
 'alternating':('stieltjes-harmonic-resonance/continuations/alternating-tails-spectral-defects',[['verification/run_all.py']]),
 'determinants':('stieltjes-harmonic-resonance/continuations/finite-difference-determinants',[['verification/verify_exact.py'],['verification/verify_numeric.py'],['identity_cli.py','--rank','3','--order','3','--shift','1']]),
 'quadratic':('stieltjes-correlation-calculus/continuations/higher-quadratic-jets',[['verification/check_exact.py'],['verification/check_numeric.py','--part','all']]),
 'spectral':('stieltjes-correlation-calculus/continuations/higher-spectral-defects',[['code/verify_exact.py'],['code/verify_numeric.py','--dps','45']]),
 'quartic':('stieltjes-harmonic-resonance/continuations/quartic-spectral-reconstruction',[['verification/run_all.py']])}
a=argparse.ArgumentParser();a.add_argument('--part',choices=plans,required=True);args=a.parse_args();folder,jobs=plans[args.part];source=B.parent/'reports'/folder
if sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
root=Path(tempfile.mkdtemp(prefix='polylog-seventeenth-'+args.part+'-'))/'package';shutil.copytree(source,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
out=V/'seventeenth-replay'/args.part;out.mkdir(parents=True,exist_ok=True);started=time.time_ns();commands=[]
(V/'.scratch-real-orders'/('seventeenth-replay-'+args.part+'-location.json')).write_text(json.dumps(dict(source=str(source),copy=str(root)),indent=2)+'\n',encoding='utf-8')
env=dict(os.environ,PYTHONUTF8='1',PYTHONIOENCODING='utf-8',PYTHONDONTWRITEBYTECODE='1',PYTHONOPTIMIZE='0')
for i,command in enumerate(jobs,1):
 step=time.time_ns();print(args.part,'running',command,flush=True)
 p=subprocess.run([sys.executable,*command],cwd=root,env=env,capture_output=True,text=True,encoding='utf-8')
 (out/(str(i)+'-run.txt')).write_text(p.stdout+p.stderr,encoding='utf-8');commands.append(dict(arguments=command,exit_code=p.returncode));print(args.part,'exit',p.returncode,flush=True)
 if p.returncode:print((p.stdout+p.stderr)[-5000:],flush=True);raise SystemExit(p.returncode)
 for q in root.rglob('*.json'):
  if q.stat().st_mtime_ns<step:continue
  target=out/'steps'/str(i)/q.relative_to(root);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target)
fresh=[]
for q in sorted(root.rglob('*.json')):
 if q.stat().st_mtime_ns<started:continue
 rel=q.relative_to(root);target=out/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target);fresh.append(rel.as_posix())
record=dict(part=args.part,source_folder=folder,commands=commands,fresh_result_files=fresh,source_code_sha256={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in source.rglob('*.py')},passed=True,scope='Complete specified mathematical suites, freshly run on a copy with assertions and UTF-8 enabled. Per-command outputs retained separately. Exact finite assertions, numerical diagnostics and canonical analytic acceptance have separate scopes. No package-manifest validation or original document rebuild is performed.')
(out/'replay-summary.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print(args.part,'complete;',len(fresh),'fresh receipts',flush=True)
