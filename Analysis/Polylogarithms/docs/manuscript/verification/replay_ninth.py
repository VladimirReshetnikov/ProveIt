"""Replay new continuation suites on isolated copies; preserve delivered evidence."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,time
B=Path(__file__).resolve().parents[1];V=B/'verification'
plans={'gauss': ('stieltjes-harmonic-resonance/continuations/gauss-hurwitz-pole-cancellation', [['code/verify_exact.py'], ['code/verify_numeric.py']]), 'mellin': ('stieltjes-correlation-calculus/continuations/mellin-lerch-dilation', [['code/exact_identity_engine.py'], ['code/verify_mellin_rows.py'], ['code/verify_mellin_master.py'], ['code/derive_parity.py'], ['code/check_dilated_polygamma.py'], ['code/check_dilated_stieltjes.py'], ['code/check_jets_section.py'], ['code/check_pi_squared.py'], ['code/summarize_verification.py']]), 'nested': ('stieltjes-harmonic-resonance/continuations/nested-harmonic-jets', [['code/run_checks.py']]), 'critical': ('uniform-transition-continuation/continuations/polylog-stieltjes-critical-transition', [['code/reproduce.py', '--suite', 'all']]), 'harmonic': ('stieltjes-harmonic-resonance/continuations/stieltjes-harmonic-identities', [['code/run_checks.py']])}
ap=argparse.ArgumentParser();ap.add_argument('--part',choices=plans,required=True)
ap.add_argument('--resume-terminal-failure',action='store_true')
ap.add_argument('--fresh-run',action='store_true');a=ap.parse_args()
name,jobs=plans[a.part];source=B.parent/'reports'/name
root=V/'.scratch-ninth'/a.part;out=V/'ninth-replay'/a.part
if a.fresh_run:root=root.with_name(a.part+'-'+str(time.time_ns()))
root.parent.mkdir(parents=True,exist_ok=True);out.mkdir(parents=True,exist_ok=True)
if root.exists():
    assert a.resume_terminal_failure,'Do not overwrite a prior/live replay; inspect its state first.'
else:shutil.copytree(source,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
started=time.time_ns();commands=[]
env=dict(os.environ,PYTHONUTF8='1',PYTHONIOENCODING='utf-8',PYTHONDONTWRITEBYTECODE='1')
local=V/'.scratch-plotdeps'
if local.is_dir():env['PYTHONPATH']=str(local)+os.pathsep+env.get('PYTHONPATH','')
for i,argv in enumerate(jobs):
    proc=subprocess.run([sys.executable,*argv],cwd=root,env=env,capture_output=True,text=True,encoding='utf-8',errors='replace')
    (out/(str(i+1)+'-'+Path(argv[-1] if argv[0]=='-O' else argv[0]).stem+('-optimized' if argv[0]=='-O' else '')+'-run.txt')).write_text((proc.stdout+proc.stderr).rstrip()+'\n',encoding='utf-8')
    commands.append(dict(arguments=argv,exit_code=proc.returncode))
    print(a.part,argv[0],'exit',proc.returncode,flush=True)
    if proc.returncode:raise RuntimeError('Replay failed; inspect '+str(out))
    if a.part=='algebra' and '--numeric-only' in argv:
        precision=argv[argv.index('--dps')+1]
        q=out/'verification'/('numeric_results_'+precision+'dps.json');q.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(root/'verification/numeric_results.json',q)
fresh=[]
for p in sorted(root.rglob('*')):
    if not p.is_file() or p.suffix not in {'.json','.jsonl'}:continue
    if p.stat().st_mtime_ns<started:continue
    rel=p.relative_to(root);q=out/rel;q.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(p,q);fresh.append(rel.as_posix())
if a.part=='algebra':fresh.extend(['verification/numeric_results_40dps.json','verification/numeric_results_50dps.json'])
manifest={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(source.rglob('*.py'))}
(out/'replay-summary.json').write_text(json.dumps(dict(part=a.part,source_folder=name,source_code_sha256=manifest,
    commands=commands,fresh_result_files=fresh,passed=all(c['exit_code']==0 for c in commands),
    scope='Fresh exact/symbolic suites and separately labeled diagnostics. Successful finite replay does not complete analytic integration or establish numerical period identities.'),indent=2)+'\n',encoding='utf-8')
print(a.part,'completed;',len(fresh),'fresh JSON receipts.')
