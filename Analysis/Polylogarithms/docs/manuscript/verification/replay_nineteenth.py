"""Full supplied mathematical suites on fresh isolated report copies.

Package checksum-manifest programs and original PDF builds are excluded.
The intentionally failed preliminary balanced-polylogarithm diagnostics are
preserved as historical evidence, separately from the corrected suites.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
B=Path(__file__).resolve().parents[1];V=B/'verification'
H='stieltjes-harmonic-resonance/continuations/';C='stieltjes-correlation-calculus/continuations/'
plans={
 'balanced':(C+'balanced-stieltjes-moments',[[f'code/{p}.py'] for p in ['verify_exact','verify_numeric','verify_special','verify_log_moments']]),
 'boundary':(C+'boundary-contacts-log-spectra',[['verification/run_all.py']]),
 'connected':(C+'connected-spectral-gamma',[[f'verification/{p}.py'] for p in ['verify','verify_supplemental','export_tables']]),
 'colored':(H+'gamma-normalizations-colored-moments',[[f'verification/{p}.py'] for p in ['verify_gamma_normalization','verify_gaussian_moments','verify_colored_moments','verify_two_clusters','verify_two_cluster_negative']]+[['verification/verify_depth_two.py','--numeric'],['verification/verify_family2_bridge.py']]),
 'gap-six':(H+'gap-six-harmonic-determinants',[['verification/run_all.py']]),
 'lattice':(C+'lattice-contacts-mixed-zeta',[['run_checks.py']]),
 'selectors':(H+'lerch-selectors',[[f'scripts/{p}.py'] for p in ['verify_exact','verify_numeric','verify_coefficient_problem']]),
 'order-ten':(H+'order-ten-stieltjes-generators',[['verification/run_all.py']]),
 'ordered':(C+'ordered-boundary-identities',[['verification/run_verification.py','--full','--asymptotics']]),
 'joint':(H+'joint-polygamma-multiscale',[
  dict(kind='cpp',source='verification/verify_gap_eight.cpp',arguments=['4','8192'],output='verification/gap_eight_certificate.json'),
  ['verification/verify_gap_eight_bridge.py'],['verification/create_gap_eight_example.py'],
  ['verification/verify_gamma_cumulants.py','--dps','36','--nodes','56','--output','verification/gamma_cumulant_checks.json'],
  ['verification/verify_gamma_cumulants.py','--dps','46','--nodes','72','--output','verification/gamma_cumulant_checks_46dps.json'],
  ['verification/stieltjes_contacts.py'],['verification/verify_stieltjes_contacts.py'],['verification/identity_audit.py']]),
 'universal':(H+'universal-gamma-coefficients',[[f'code/{p}.py'] for p in ['check_universal','check_exact','check_applications','check_numeric']]),
 'beta':(H+'universal-beta-normal-forms',[['verification/check_exact.py'],['verification/check_analytic.py']])}
a=argparse.ArgumentParser();a.add_argument('--part',choices=plans,required=True);a.add_argument('--repair-receipt-path',action='store_true');args=a.parse_args();folder,jobs=plans[args.part];source=B.parent/'reports'/folder
if sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
root=Path(tempfile.mkdtemp(prefix='polylog-nineteenth-'+args.part+'-'))/'package';shutil.copytree(source,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
out=V/'nineteenth-replay'/args.part;out.mkdir(parents=True,exist_ok=True);started=time.time_ns();commands=[]
repairs=[]
if args.repair_receipt_path:
 assert args.part=='lattice'
 name='verification/check_mixed_tails_numeric.py';p=root/name;text=p.read_text(encoding='utf-8')
 old="Path(__file__).resolve().parents[1]/'results'/'mixed_tail_numeric.json'.write_text"
 new="(Path(__file__).resolve().parents[1]/'results'/'mixed_tail_numeric.json').write_text"
 assert text.count(old)==1;p.write_text(text.replace(old,new),encoding='utf-8')
 repairs.append(dict(path=name,original_source_sha256=hashlib.sha256((source/name).read_bytes()).hexdigest(),copy_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),change='Parenthesize the composed output Path before write_text. No mathematical expression changes.'))
 (out/'receipt-path-copy-only.patch').write_text('- '+old+'\n+ '+new+'\n',encoding='utf-8')
(V/'.scratch-real-orders'/('nineteenth-replay-'+args.part+'-location.json')).write_text(json.dumps(dict(source=str(source),copy=str(root)),indent=2)+'\n',encoding='utf-8')
env=dict(os.environ,PYTHONUTF8='1',PYTHONIOENCODING='utf-8',PYTHONDONTWRITEBYTECODE='1',PYTHONOPTIMIZE='0')
for i,job in enumerate(jobs,1):
 step=time.time_ns();print(args.part,'running',job,flush=True)
 if isinstance(job,dict):
  binary=root/'fresh-gap-eight.exe';compiler=shutil.which('g++');assert compiler
  p=subprocess.run([compiler,'-O3','-std=c++17','-Wall','-Wextra','-pedantic',str(root/job['source']),'-o',str(binary)],cwd=root,env=env,capture_output=True,text=True,encoding='utf-8');(out/(str(i)+'-compiler.txt')).write_text(p.stdout+p.stderr,encoding='utf-8');assert p.returncode==0,p.stderr
  p=subprocess.run([str(binary),*job['arguments']],cwd=root,env=env,capture_output=True,text=True,encoding='utf-8')
  assert p.returncode==0,p.stderr
  generated=json.loads(p.stdout);original=json.loads((source/job['output']).read_text(encoding='utf-8'));assert generated==original
  (root/job['output']).write_text(json.dumps(generated,indent=2)+'\n',encoding='utf-8')
 else:p=subprocess.run([sys.executable,*job],cwd=root,env=env,capture_output=True,text=True,encoding='utf-8')
 (out/(str(i)+'-run.txt')).write_text(p.stdout+p.stderr,encoding='utf-8');commands.append(dict(arguments=job,exit_code=p.returncode));print(args.part,'exit',p.returncode,flush=True)
 if p.returncode:print((p.stdout+p.stderr)[-6000:],flush=True);raise SystemExit(p.returncode)
 for q in root.rglob('*.json'):
  if q.stat().st_mtime_ns<step:continue
  target=out/'steps'/str(i)/q.relative_to(root);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target)
fresh=[]
for q in sorted(root.rglob('*.json')):
 if q.stat().st_mtime_ns<started:continue
 rel=q.relative_to(root);target=out/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target);fresh.append(rel.as_posix())
record=dict(part=args.part,source_folder=folder,commands=commands,fresh_result_files=fresh,copy_only_repairs=repairs,source_code_sha256={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in source.rglob('*') if p.is_file() and p.suffix in ('.py','.cpp')},passed=True,scope='Complete specified mathematical suites, freshly run on isolated copies with assertions and UTF-8 enabled. Any copy-only source repair is explicitly recorded, with original delivered source retained. Exact finite assertions, numerical diagnostics and canonical analytic acceptance are separate. The joint suite freshly compiles and reproduces the entire exact gap-eight certificate. No package-manifest verification or original document rebuild is performed.')
(out/'replay-summary.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8');print(args.part,'complete;',len(fresh),'fresh receipts',flush=True)
