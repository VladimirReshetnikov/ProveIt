"""Full mathematical replay of the fifteenth intake, only on fresh copies."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
B=Path(__file__).resolve().parents[1];V=B/'verification'
plans={'bernoulli': ('stieltjes-harmonic-resonance/continuations/bernoulli-tornheim-digamma', [['verification/verify_all.py', '--numerical']]), 'cubic': ('stieltjes-harmonic-resonance/continuations/cubic-tail-descent', [['verification/verify.py', '--exact-only'], ['verification/verify.py', '--numeric-only', '--dps', '50']]), 'determinantal': ('stieltjes-harmonic-resonance/continuations/determinantal-harmonic-resonance', [['code/verify_exact.py'], ['code/verify_numeric.py']]), 'differential': ('stieltjes-harmonic-resonance/continuations/differential-polygamma-lerch-jets', [['verify_all.py', '--full']]), 'multishift': ('stieltjes-correlation-calculus/continuations/multishift-reflection', [['code/verify_exact.py'], ['code/verify_numeric.py', '--dps', '45'], ['code/verify_numeric.py', '--dps', '60']]), 'tails': ('stieltjes-harmonic-resonance/continuations/polygamma-tail-identities', [['code/run_verification.py', '--full']])}
a=argparse.ArgumentParser();a.add_argument('--part',choices=plans,required=True);args=a.parse_args();folder,jobs=plans[args.part];source=B.parent/'reports'/folder
root=Path(tempfile.mkdtemp(prefix='polylog-fifteenth-'+args.part+'-'))/'package';shutil.copytree(source,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc'));out=V/'fifteenth-replay'/args.part;out.mkdir(parents=True,exist_ok=True);assert not os.environ.get('PYTHONOPTIMIZE');started=time.time_ns();commands=[]
(V/'.scratch-real-orders'/('fifteenth-replay-'+args.part+'-location.json')).write_text(json.dumps(dict(source=str(source),copy=str(root)),indent=2)+'\n',encoding='utf-8')
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
