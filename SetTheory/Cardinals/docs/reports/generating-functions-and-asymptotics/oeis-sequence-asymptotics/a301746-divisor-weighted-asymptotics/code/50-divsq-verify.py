#!/usr/bin/env python3
"""Verify immutable A301746 report, proof pins, and fresh exact/numerical checks."""
import sys
if not __debug__:raise SystemExit('Assertions must be enabled; do not use -O.')
from pathlib import Path
import hashlib,json,os,subprocess,tempfile,time
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):return json.loads(p.read_text())
def pin(rel,digest):
 p=ROOT/rel;assert p.is_file() and not p.is_symlink(),rel
 assert sha(p)==digest,(rel,digest)
def tree():return {p.relative_to(ROOT).as_posix():sha(p) for p in ROOT.rglob('*') if p.is_file()}
def main():
 start=time.monotonic();before=tree();manifest={}
 for line in (ROOT/'SHA256SUMS').read_text().splitlines():
  digest,rel=line.split('  ',1);p=Path(rel)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in rel and rel not in manifest
  manifest[rel]=digest;pin(rel,digest)
 assert set(manifest)==set(before)-{'SHA256SUMS'},'Manifest coverage mismatch'
 r=load(ROOT/'audits/independent/approval.json');assert r['status']=='APPROVED';pins=0
 for name,h in r['source_sha256'].items():pin('proofs/'+name,h);pins+=1
 for name,h in r['files'].items():pin('audits/independent/'+name,h);pins+=1
 i=load(ROOT/'audits/integrated_approval.json');assert i['status']=='APPROVED'
 for name,h in i['files'].items():
  rel=name if name.startswith('article/') else ('proofs/'+name if name=='NUMERICAL_SUMMARY.md' else 'checks/producer/'+name)
  pin(rel,h);pins+=1
 pin('audits/independent/approval.json',i['earlier_approval_sha256']);pins+=1
 pin('audits/INTEGRATED_REVIEW.md',i['review_sha256']);pins+=1
 visual=load(ROOT/'audits/root-visual-approval.json');assert visual['status']=='APPROVED'
 pin('article/divisor-square-partitions.tex',visual['source_sha256']);pin('article/divisor-square-partitions.pdf',visual['pdf_sha256']);pins+=2
 qa=load(ROOT/'article/visual-qa.json');assert qa['status']=='passed' and qa['page_count']==10 and qa['all_pages_visually_inspected']
 pin('article/divisor-square-partitions.tex',qa['source_sha256']);pin('article/divisor-square-partitions.pdf',qa['pdf_sha256']);pins+=2
 jobs=[('checks/producer/verify.py','checks/producer/verification.json','verification.json'),('checks/producer/verify_log_series.py','checks/producer/log_series_verification.json','log_series_verification.json'),('audits/independent/check.py','audits/independent/verification.json','verification.json')]
 with tempfile.TemporaryDirectory(prefix='a301746-portable-replay-') as tmp:
  for j,(script,expected,output) in enumerate(jobs):
   dest=Path(tmp)/str(j);env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
   run=subprocess.run([sys.executable,str(ROOT/script),'--output-dir',str(dest)],cwd=tmp,env=env,capture_output=True,text=True)
   assert run.returncode==0,(script,run.stdout,run.stderr)
   assert load(dest/output)==load(ROOT/expected),('Receipt mismatch',script)
   neg=subprocess.run([sys.executable,'-O',str(ROOT/script),'--output-dir',str(Path(tmp)/('negative'+str(j)))],cwd=tmp,env=env,capture_output=True,text=True)
   assert neg.returncode!=0 and ('-O' in neg.stdout+neg.stderr or 'Assertions' in neg.stdout+neg.stderr),(script,'Optimization accepted')
   print('PASS',script,flush=True)
 import sympy as S
 r,c,d=S.symbols('r c d');sym=load(ROOT/'checks/producer/log_series_verification.json');exact=load(ROOT/'audits/independent/verification.json')['formal_coefficients'];comparisons=0
 for label,key in [('forward','forward_coefficients'),('inverse','inverse_coefficients')]:
  assert set(sym[key])==set(exact[label])
  for j,expr in sym[key].items():
   value=0
   for powers,co in exact[label][j].items():
    a,b,e=map(int,powers.split(','));value+=S.Rational(co)*r**a*c**b*d**e
   assert S.expand(S.sympify(expr)-value)==0,(label,j)
   comparisons+=1
 assert tree()==before,'Packaged files changed during replay'
 print(json.dumps({'status':'PASS','manifest_files':len(manifest),'approval_pin_checks':pins,'checkers':len(jobs),'formal_cross_comparisons':comparisons,'all_optimization_gates_rejected':True,'immutable':True,'seconds':round(time.monotonic()-start,3)},indent=2))
if __name__=='__main__':main()
