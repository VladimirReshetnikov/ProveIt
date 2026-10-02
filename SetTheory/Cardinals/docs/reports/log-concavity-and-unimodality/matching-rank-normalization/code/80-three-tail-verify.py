#!/usr/bin/env python3
"""Read-only replay of the attributed rank-boundary comparison and exact corroboration."""
if not __debug__:raise SystemExit('Run without -O: assertions are required.')
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time,zipfile,stat
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def canonical(v):
 if isinstance(v,dict):return {k:canonical(x) for k,x in v.items() if k not in {'seconds','elapsed_seconds'}}
 if isinstance(v,list):return [canonical(x) for x in v]
 return v

def manifest():
 records={}
 for line in (ROOT/'SHA256SUMS').read_text().splitlines():
  h,n=line.split('  ',1);p=Path(n)
  assert not p.is_absolute() and '..' not in p.parts and n not in records,n
  assert sha(ROOT/p)==h,n;records[n]=h
 actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}
 assert actual==set(records),'Manifest coverage is not exact'
 return records

def pinned(name,h):
 p=ROOT/name
 if not Path(name).is_absolute() and p.is_file():assert sha(p)==h,name;return
 matches=[p for p in ROOT.rglob(Path(name).name) if p.is_file() and sha(p)==h]
 assert len(matches)==1,(name,h,len(matches))

def approval(path):
 data=json.loads(path.read_text())
 if 'earlier_audit_receipt_sha256' in data:pinned('approval_receipt.json',data['earlier_audit_receipt_sha256'])
 if 'source_sha256' in data:pinned(data.get('source',data.get('reviewed_source','THREE_TAIL_OBSTRUCTION.md')),data['source_sha256'])
 for group in ('files','artifacts','supplementary_checks','dependencies'):
  for name,h in data.get(group,{}).items():pinned(name,h)
 return data

def run(script,cwd,args=()):
 out=subprocess.run([sys.executable,str(script),*map(str,args)],cwd=cwd,text=True,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
 if out.returncode:
  print(out.stdout);print(out.stderr,file=sys.stderr);raise AssertionError(script.name)
 return out.stdout

def dependency(work):
 archive=ROOT/'dependencies/two-element-matroid-lorentzian-result.zip'
 assert sha(archive)=='56e7c88467750b725d99cf17021b5cfe770e32d243c356e0206762f04479bf55'
 with zipfile.ZipFile(archive) as z:
  seen=set()
  for info in z.infolist():
   p=Path(info.filename);mode=info.external_attr>>16
   assert not p.is_absolute() and '..' not in p.parts and '\\' not in info.filename
   assert info.filename not in seen and not info.flag_bits&1
   assert not stat.S_ISLNK(mode) and (not stat.S_IFMT(mode) or stat.S_ISREG(mode))
   seen.add(info.filename)
  assert z.testzip() is None
  z.extractall(work)
 nested=work/'two-element-matroid-lorentzian-result'
 assert (nested/'article/two-element-matroid-lorentzian.pdf').read_bytes()==(ROOT/'dependencies/rank-five-proof.pdf').read_bytes()
 before={p.relative_to(nested).as_posix():sha(p)for p in nested.rglob('*')if p.is_file()}
 output=run(nested/'verify.py',nested);print(output,flush=True)
 assert before=={p.relative_to(nested).as_posix():sha(p)for p in nested.rglob('*')if p.is_file()}
 bad=subprocess.run([sys.executable,'-O',str(nested/'verify.py')],cwd=nested,capture_output=True)
 assert bad.returncode!=0
 print('PASS: exact frozen dependency, readable PDF identity, safe extraction, complete nested replay and immutability',flush=True)

def main():
 start=time.monotonic();original=manifest();print(f'PASS: {len(original)} file hashes and exact manifest coverage',flush=True)
 
 for name in ('scalar/approval.json','obstruction/approval.json','first-layer/root_approval.json','first-layer/cubic_approval.json','direct-union/approval.json'):approval(ROOT/'audits'/name)
 assert (ROOT/'audits/integrated-approval.json').is_file(),'Integrated approval is required'
 approval(ROOT/'audits/integrated-approval.json')
 qa=json.loads((ROOT/'qa/visual-qa.json').read_text());assert qa['pdf_sha256']==sha(ROOT/'article/sharp-weighted-rank-boundary.pdf');assert qa['pages_visually_inspected']==list(range(1,qa['pages']+1))
 print('PASS: independent and integrated approval pins; all-page QA hash',flush=True)
 jobs=[('scalar','check.py','verification.json',()),('obstruction','check.py','verification.json',()),('obstruction','check_abstract.py','abstract_verification.json',()),('obstruction','check_diagonal.py','diagonal_verification.json',()),('first-layer','check.py','verification.json',()),('first-layer','check_general.py','general_verification.json',()),('direct-union','check.py','verification.json',())]
 with tempfile.TemporaryDirectory(prefix='sharp-rank-boundary-replay-') as temp:
  dep=Path(temp)/'dependency';dep.mkdir();dependency(dep)
  for i,(group,script,receipt,extra) in enumerate(jobs):
   work=Path(temp)/str(i);work.mkdir();source=ROOT/'reproducibility'/group/script;copied=work/script;shutil.copyfile(source,copied)
   run(copied,work,[*extra,'--output-dir',work])
   actual=json.loads((work/receipt).read_text());expected=json.loads(source.with_name(receipt).read_text())
   assert canonical(actual)==canonical(expected),(group,script,'deterministic receipt mismatch')
   optimized=subprocess.run([sys.executable,'-O',str(copied),*map(str,extra),'--output-dir',str(work)],cwd=work,text=True,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
   assert optimized.returncode!=0,(group,script,'optimization should be rejected')
   print(f'PASS: {group}/{script}; deterministic receipt and -O gate',flush=True)
 assert manifest()==original,'Replay changed the release'
 print(json.dumps({'status':'PASS','manifest_files':len(original),'new_checkers':len(jobs),'nested_checkers':4,'all_deterministic_receipts_match':True,'all_optimization_gates_pass':True,'released_files_unchanged':True,'seconds':round(time.monotonic()-start,3)},indent=2))
if __name__=='__main__':main()
