"""Replay each twentieth-intake mathematical suite on a fresh isolated copy.

Original records, sources and PDFs remain unchanged. Package-manifest checks
and PDF builds are outside this mathematical replay. Finite checks and
floating-point diagnostics do not establish an all-order analytic theorem.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
B=Path(__file__).resolve().parents[1];V=B/'verification'
H='stieltjes-harmonic-resonance/continuations/'
plans={
 'cubic':('cubic-gamma-normal-form',[[f'verification/{p}.py'] for p in ['verify_exact','verify_endpoints','exploratory_all_orders','verify_numeric']]),
 'higher':('higher-identities',[['reproduce.py','--exact','--numeric'],['code/normal_forms/check_compensator_signs.py']]),
 'anchors':('mixed-tail-anchor-reductions',[['verification/run_all.py']]),
 'hankel':('rational-hankel-polylogarithms',[['verify_all.py']]),
 'universal':('universal-gamma-coefficients-replay',[['code/verify_exact.py','--max-weight','28'],['code/verify_numeric.py']])}
a=argparse.ArgumentParser();a.add_argument('--part',choices=plans,required=True)
a.add_argument('--structured-record-comparison',action='store_true');args=a.parse_args()
if sys.flags.optimize:raise RuntimeError('Assertions must remain enabled.')
folder,jobs=plans[args.part];source=B.parent/'reports'/H/folder
root=Path(tempfile.mkdtemp(prefix='polylog-twentieth-'+args.part+'-'))/'package'
shutil.copytree(source,root,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
out=V/'twentieth-replay'/args.part;out.mkdir(parents=True,exist_ok=True)
started=time.time_ns();commands=[]
repairs=[]
if args.structured_record_comparison:
 assert args.part=='higher'
 p=root/'reproduce.py';text=p.read_text(encoding='utf-8')
 old="""            if generated.read_bytes() != supplied.read_bytes():
                raise AssertionError('Generated record differs: ' + relative)"""
 new="""            if generated.suffix == '.csv':
                import csv
                with generated.open(encoding='utf-8', newline='') as f:
                    actual = list(csv.reader(f))
                with supplied.open(encoding='utf-8', newline='') as f:
                    expected = list(csv.reader(f))
            elif generated.suffix == '.json':
                actual = json.loads(generated.read_text(encoding='utf-8'))
                expected = json.loads(supplied.read_text(encoding='utf-8'))
                if relative == 'code/gap_ten/gap_ten_independent_checks.json':
                    records.append({'name': 'certificate-serialization-identifiers',
                                    'generated': actual.pop('sha256'),
                                    'supplied': expected.pop('sha256'),
                                    'scope': 'Descriptive byte identifiers retained separately; every CSV field was already compared exactly.'})
            else:
                actual, expected = generated.read_bytes(), supplied.read_bytes()
            if actual != expected:
                raise AssertionError('Generated structured record differs: ' + relative)"""
 assert text.count(old)==1;p.write_text(text.replace(old,new),encoding='utf-8')
 repairs.append(dict(path='reproduce.py',original_source_sha256=hashlib.sha256((source/'reproduce.py').read_bytes()).hexdigest(),copy_source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),change='Compare every CSV field and mathematical JSON value exactly on the isolated copy. Retain the descriptive CSV byte identifiers separately instead of treating serialization as a mathematical value. No mathematical computation or certificate value changes; other comparisons retain exact bytes.'))
 (out/'structured-record-copy-only.patch').write_text('- '+old+'\n+ '+new+'\n',encoding='utf-8')
(V/'.scratch-real-orders'/('twentieth-replay-'+args.part+'-location.json')).write_text(json.dumps(dict(source=str(source),copy=str(root)),indent=2)+'\n',encoding='utf-8')
env=dict(os.environ,PYTHONUTF8='1',PYTHONIOENCODING='utf-8',PYTHONDONTWRITEBYTECODE='1',PYTHONOPTIMIZE='0')
for i,job in enumerate(jobs,1):
 step=time.time_ns();print(args.part,'running',job,flush=True)
 p=subprocess.run([sys.executable,*job],cwd=root,env=env,capture_output=True,text=True,encoding='utf-8')
 (out/(str(i)+'-run.txt')).write_text(p.stdout+p.stderr,encoding='utf-8')
 commands.append(dict(arguments=job,exit_code=p.returncode));print(args.part,'exit',p.returncode,flush=True)
 if p.returncode:
  (out/'failure-summary.json').write_text(json.dumps(dict(part=args.part,commands=commands,copy_only_repairs=repairs,passed=False,scope='The original wrapper stopped at this step. Later checks are not claimed as passed.'),indent=2)+'\n',encoding='utf-8')
  print((p.stdout+p.stderr)[-6000:],flush=True);raise SystemExit(p.returncode)
 for q in root.rglob('*.json'):
  if q.stat().st_mtime_ns<step:continue
  target=out/'steps'/str(i)/q.relative_to(root);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target)
fresh=[]
for q in sorted(root.rglob('*.json')):
 if q.stat().st_mtime_ns<started:continue
 rel=q.relative_to(root);target=out/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(q,target);fresh.append(rel.as_posix())
record=dict(part=args.part,source_folder=H+folder,commands=commands,fresh_result_files=fresh,copy_only_repairs=repairs,source_code_sha256={p.relative_to(source).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in source.rglob('*') if p.is_file() and p.suffix in ('.py','.cpp')},passed=True,scope='Complete specified mathematical suites, freshly run on isolated copies with assertions and UTF-8 enabled. The higher-identities wrapper independently copies code, freshly compiles and reproduces every field of the full gap-ten CSV, and compares exact subsidiary JSON values. Any portable structured-record comparison is explicitly recorded as a copy-only harness change. Original deliveries are unchanged. Conjectural support/sign probes remain finite evidence; numerical outputs are not certified enclosures. No package-manifest verification or document rebuild is performed.')
(out/'replay-summary.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
print(args.part,'complete;',len(fresh),'fresh JSON receipts',flush=True)
