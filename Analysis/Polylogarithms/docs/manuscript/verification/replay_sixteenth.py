"""Full mathematical replay of the sixteenth intake, only on fresh copies."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
B=Path(__file__).resolve().parents[1];V=B/'verification'
plans={'beta': ('stieltjes-correlation-calculus/continuations/beta-crossing', [['verification/check_exact.py'], ['verification/check_numeric.py', '--dps', '65']]), 'gamma': ('stieltjes-harmonic-resonance/continuations/harmonic-tail-gamma', [['verification/run_all.py']]), 'shifts': ('stieltjes-harmonic-resonance/continuations/harmonic-tails-shifts-twists', [['verification/verify_gap_four.py', '--output', 'results/gap_four_exact_results.json'], ['verification/verify_shifted_tails.py', '--output', 'results/shifted_tail_results.json'], ['verification/verify_alternating_master.py', '--numeric', '--output', 'results/alternating_verification.json']]), 'reconstruction': ('stieltjes-harmonic-resonance/continuations/polygamma-reconstruction-resonance', [['verification/run_checks.py']]), 'quadratic': ('stieltjes-correlation-calculus/continuations/quadratic-spectrum-stieltjes', [['code/verify_exact.py', '--output', 'data/exact_replay.json'], ['code/verify_numeric.py', '--dps', '45', '--output', 'data/numeric_replay.json']]), 'same-direction': ('stieltjes-correlation-calculus/continuations/same-direction-complex-orders', [['code/verify_exact.py'], ['code/verify_numeric.py', '--part', 'all']])}
a=argparse.ArgumentParser();a.add_argument('--part',choices=plans,required=True);args=a.parse_args();folder,jobs=plans[args.part];source=B.parent/'reports'/folder
root=Path(tempfile.mkdtemp(prefix='polylog-sixteenth-'+args.part+'-'))/'package';shutil.copytree(source,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));out=V/'sixteenth-replay'/args.part;out.mkdir(parents=True,exist_ok=True);assert not os.environ.get('PYTHONOPTIMIZE');started=time.time_ns();commands=[]
(V/'.scratch-real-orders'/('sixteenth-replay-'+args.part+'-location.json')).write_text(json.dumps(dict(source=str(source),copy=str(root)),indent=2)+'\n',encoding='utf-8')
env=dict(os.environ,PYTHONUTF8='1',PYTHONIOENCODING='utf-8',PYTHONDONTWRITEBYTECODE='1')
for i,command in enumerate(jobs,1):
    step=time.time_ns();print(args.part,'running',command,flush=True);p=subprocess.run([sys.executable,*command],cwd=root,env=env,capture_output=True,text=True,encoding='utf-8');(out/(str(i)+'-run.txt')).write_text(p.stdout+p.stderr,encoding='utf-8');commands.append(dict(arguments=command,exit_code=p.returncode));print(args.part,'exit',p.returncode,flush=True)
    if p.returncode:print((p.stdout+p.stderr)[-5000:],flush=True);raise SystemExit(p.returncode)
    for q in root.rglob('*.json'):
        if q.stat().st_mtime_ns<step:continue
        target=out/'steps'/str(i)/q.relative_to(root);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target)
fresh=[]
for q in sorted(root.rglob('*.json')):
    if q.stat().st_mtime_ns<started:continue
    rel=q.relative_to(root);target=out/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target);fresh.append(rel.as_posix())
record=dict(part=args.part,source_folder=folder,commands=commands,fresh_result_files=fresh,source_code_sha256={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in source.rglob('*.py')},passed=True,scope='Complete specified mathematical suites, freshly run on a copy. Earlier per-command JSON outputs are also retained under steps, including both tilted numerical precisions. Exact finite assertions, diagnostics and canonical analytic acceptance have separate scopes.')
(out/'replay-summary.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print(args.part,'complete;',len(fresh),'fresh receipts',flush=True)
