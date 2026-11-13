from pathlib import Path
import subprocess,sys,json,concurrent.futures
ROOT=Path(__file__).resolve().parent
SRC=ROOT/'tests/compact/byte/inherited'
files=sorted(SRC.rglob('*.json'))
programs={'control':ROOT/'controls/bytes487.py','candidate':ROOT/'code/checker_bytes.py'}
def task(t):
 p,opt=t;out={}
 for name,f in programs.items():
  r=subprocess.run([sys.executable,'-I','-S','-B']+(['-O'] if opt else [])+[str(f)],input=p.read_bytes(),capture_output=True,timeout=20)
  out[name]=r.returncode==0 and r.stdout==b'ACCEPT\n'
 return {'fixture':str(p.relative_to(SRC)),'optimized':opt,**out}
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool: rows=list(pool.map(task,[(p,opt) for p in files for opt in (False,True)]))
fails=[x for x in rows if x['control']!=x['candidate']]
report={'fixtures':len(files),'process_executions':len(rows)*2,'mismatches':fails,'results':rows}
(ROOT/'evidence/byte_validation.json').write_text(json.dumps(report,indent=2)+'\n')
print({k:v for k,v in report.items() if k!='results'})
assert not fails
