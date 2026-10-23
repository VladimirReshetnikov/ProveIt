#!/usr/bin/env python3
"""Read-only original-family audit, with all execution in an isolated copy."""
from pathlib import Path
import concurrent.futures,hashlib,importlib.metadata,json,platform,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'root_checks'
SNAP=Path(tempfile.mkdtemp(prefix='wave8_dependency_'));print('snapshot',SNAP,flush=True)
FAMILIES=['encoding','sun','nine','signed','positive','short']
inputs={}
for fam in FAMILIES:
 src=ROOT/fam;dst=SNAP/fam
 shutil.copytree(src,dst,ignore=shutil.ignore_patterns('__pycache__','*.pyc','render','*.aux','*.out','*.log'))
 inputs[fam]={str(p.relative_to(dst)):hashlib.sha256(p.read_bytes()).hexdigest() for p in dst.rglob('*') if p.is_file()}
(OUT/'DEPENDENCY_INPUT_HASHES.json').write_text(json.dumps(inputs,indent=2)+'\n')
CASES={
 'encoding':[('verify_split.py',False),('verify_split.py',True),('test_split.py',False),('test_split.py',True)],
 'sun':[('reproduce.py',False),('independent_check.py',True)],
 'nine':[('verify_nine.py',False),('verify_nine.py',True),('independent_review.py',False),('independent_review.py',True)],
 'signed':[('check_jones.py',False),('check_jones.py',True),('check_source_minimum_independent.py',False),('check_source_minimum_independent.py',True)],
 'positive':[('build_ordinary_merger.py',False),('check_ordinary_merger.py',False),('check_ordinary_merger.py',True),('check_merger_independent.py',False),('check_merger_independent.py',True)],
 'short':[('build.py',False),('audit.py',False),('audit.py',True)]}
def run_family(fam):
 results=[]
 for script,opt in CASES[fam]:
  tag=fam+'__'+script[:-3]+('__optimized' if opt else '__normal');args=[sys.executable]+(['-O']if opt else[])+[str(SNAP/fam/script)];start=time.monotonic()
  cp=subprocess.run(args,cwd=SNAP/fam,capture_output=True,text=True,timeout=600)
  (OUT/(tag+'.stdout.txt')).write_text(cp.stdout);(OUT/(tag+'.stderr.txt')).write_text(cp.stderr)
  expected_rejection=fam=='nine' and script=='verify_nine.py' and opt
  ok=(cp.returncode!=0 and 'Run without -O/-OO' in cp.stderr) if expected_rejection else cp.returncode==0
  r=dict(family=fam,script=script,optimized=opt,returncode=cp.returncode,expected_optimized_rejection=expected_rejection,status=('EXPECTED_REJECTION'if expected_rejection else'PASS')if ok else'FAIL',elapsed_seconds=round(time.monotonic()-start,3),stdout_sha256=hashlib.sha256(cp.stdout.encode()).hexdigest(),stderr_sha256=hashlib.sha256(cp.stderr.encode()).hexdigest(),stderr_tail=cp.stderr.splitlines()[-4:])
  print(json.dumps(r),flush=True);results.append(r)
 after={str(p.relative_to(SNAP/fam)):hashlib.sha256(p.read_bytes()).hexdigest()for p in (SNAP/fam).rglob('*')if p.is_file()and'__pycache__'not in p.parts}
 changed=[n for n,h in inputs[fam].items()if after.get(n)!=h]
 return dict(family=fam,cases=results,changed_existing_files=changed,new_files=sorted(set(after)-set(inputs[fam])))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:results=list(ex.map(run_family,FAMILIES))
cases=[x for f in results for x in f['cases']]
out=dict(scope='Frozen copies of the six authored deliverable families only; no inherited upstream Python executed.',environment={'python':platform.python_version(),'implementation':platform.python_implementation(),'numpy':importlib.metadata.version('numpy')},snapshot=str(SNAP),families=results,successful_commands=sum(x['status']=='PASS'for x in cases),expected_optimized_rejections=sum(x['status']=='EXPECTED_REJECTION'for x in cases),status='PASS'if all(x['status']in['PASS','EXPECTED_REJECTION']for x in cases)and all(not f['changed_existing_files']for f in results)else'FAIL')
(OUT/'DEPENDENCY_REPLAY.json').write_text(json.dumps(out,indent=2)+'\n');print('FINAL',out['status'],flush=True)
