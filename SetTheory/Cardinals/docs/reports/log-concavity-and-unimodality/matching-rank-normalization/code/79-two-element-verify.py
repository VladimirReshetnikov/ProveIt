#!/usr/bin/env python3
"""Read-only replay of the two-element matroid theorem's exact corroboration."""
if not __debug__:raise SystemExit('Run without -O: assertions are required.')
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile,time
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
 if 'source_sha256' in data:pinned(data.get('reviewed_source','FULL_SELECTED_TAIL_THEOREM.md'),data['source_sha256'])
 for group in ('files','artifacts'):
  for name,h in data.get(group,{}).items():pinned(name,h)
 return data

def run(script,cwd,args=()):
 out=subprocess.run([sys.executable,str(script),*map(str,args)],cwd=cwd,text=True,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
 if out.returncode:
  print(out.stdout);print(out.stderr,file=sys.stderr);raise AssertionError(script.name)
 return out.stdout

def main():
 start=time.monotonic();original=manifest();print(f'PASS: {len(original)} file hashes and exact manifest coverage',flush=True)
 
 for name in ('represented/approval_receipt.json','represented/root_review.json','abstract/approval_receipt.json','abstract/padding_approval_receipt.json'):approval(ROOT/'audits'/name)
 assert (ROOT/'audits/integrated-approval.json').is_file(),'Integrated approval is required'
 approval(ROOT/'audits/integrated-approval.json')
 qa=json.loads((ROOT/'qa/visual-qa.json').read_text());assert qa['pdf_sha256']==sha(ROOT/'article/two-element-matroid-lorentzian.pdf');assert qa['pages_visually_inspected']==list(range(1,qa['pages']+1))
 print('PASS: independent and integrated approval pins; all-page QA hash',flush=True)
 jobs=[('producer','check_full_variables.py','verification.json',()),('represented','check.py','independent_receipt.json',('--source-note',ROOT/'proof-notes/FULL_SELECTED_TAIL_THEOREM.md')),('abstract','check.py','independent_receipt.json',('--source-note',ROOT/'proof-notes/ALL_MATROIDS_EXTENSION.md')),('padding','check_padding.py','padding_receipt.json',('--source-note',ROOT/'proof-notes/OLD_SPANNING_REMOVAL.md'))]
 with tempfile.TemporaryDirectory(prefix='two-element-matroid-replay-') as temp:
  for i,(group,script,receipt,extra) in enumerate(jobs):
   work=Path(temp)/str(i);work.mkdir();source=ROOT/'reproducibility'/group/script;copied=work/script;shutil.copyfile(source,copied)
   run(copied,work,[*extra,'--output-dir',work])
   actual=json.loads((work/receipt).read_text());expected=json.loads(source.with_name(receipt).read_text())
   assert canonical(actual)==canonical(expected),(group,script,'deterministic receipt mismatch')
   optimized=subprocess.run([sys.executable,'-O',str(copied),*map(str,extra),'--output-dir',str(work)],cwd=work,text=True,capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
   assert optimized.returncode!=0,(group,script,'optimization should be rejected')
   print(f'PASS: {group}/{script}; deterministic receipt and -O gate',flush=True)
 assert manifest()==original,'Replay changed the release'
 print(json.dumps({'status':'PASS','manifest_files':len(original),'checkers':len(jobs),'all_deterministic_receipts_match':True,'all_optimization_gates_pass':True,'released_files_unchanged':True,'seconds':round(time.monotonic()-start,3)},indent=2))
if __name__=='__main__':main()
