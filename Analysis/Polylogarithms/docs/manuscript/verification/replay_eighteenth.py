"""Full mathematical suites for the eighteenth intake, only on isolated copies.

Package-manifest programs and document rebuilds are deliberately outside
these mathematical replay commands; delivered files remain unchanged.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
B=Path(__file__).resolve().parents[1];V=B/'verification'
plans={'affine': ('stieltjes-harmonic-resonance/continuations/affine-gamma-polarization', [['verification/run_all.py']]), 'bernoulli': ('stieltjes-harmonic-resonance/continuations/bernoulli-tails-spectral-faces', [['verification/run_all.py', '--exact', '--numerical']]), 'bilinear': ('stieltjes-harmonic-resonance/continuations/bilinear-tails-determinants', [['verification/verify_bilinear_tails.py', 'results/bilinear_verification.json'], ['verification/verify_cutoff_jets.py', 'results/cutoff_jets_checks.json'], ['verification/determinants/verify_exact.py'], ['verification/determinants/verify_numeric.py'], ['verification/determinants/verify_polylog.py'], ['verification/order10/verify_order10_completion.py', '--full', '--output', 'results/order10_completion_checks.json'], ['verification/order10/eventual_threshold.py', '5', '--output', 'results/order10_eventual_threshold_replay.json'], ['verification/order10/build_order10_identity.py']]), 'dougall': ('stieltjes-harmonic-resonance/continuations/dougall-termination', [['code/verify_exact.py'], ['code/verify_numeric.py', '--part', '1'], ['code/verify_numeric.py', '--part', '2'], ['code/verify_numeric.py', '--part', '3']]), 'boundary': ('tail-boundaries', [['verification/tails/run_tail_checks.py', '--full'], ['verification/kernels/verify_kernels.py'], ['verification/mellin/verify_mellin_polylog.py'], ['verification/stieltjes/code/verify_stieltjes_edge.py', '--mode', 'all']]), 'vertical': ('stieltjes-correlation-calculus/continuations/vertical-lattice-jets', [['verification/run_checks.py']])}
a=argparse.ArgumentParser();a.add_argument('--part',choices=plans,required=True);args=a.parse_args();folder,jobs=plans[args.part];source=B.parent/'reports'/folder
if sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
root=Path(tempfile.mkdtemp(prefix='polylog-eighteenth-'+args.part+'-'))/'package';shutil.copytree(source,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
out=V/'eighteenth-replay'/args.part;out.mkdir(parents=True,exist_ok=True);started=time.time_ns();commands=[]
(V/'.scratch-real-orders'/('eighteenth-replay-'+args.part+'-location.json')).write_text(json.dumps(dict(source=str(source),copy=str(root)),indent=2)+'\n',encoding='utf-8')
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
