"""Authored mutation controls, run on temporary copies only."""
from pathlib import Path
import tempfile,shutil,json,subprocess,sys,os
R=Path(__file__).resolve().parent

def must_fail(root,command,token):
 p=subprocess.run([sys.executable,'-O']+command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},timeout=180)
 if not p.returncode or token not in p.stdout:raise RuntimeError('Negative control failed to detect intended defect: '+str(command)+'\n'+p.stdout[-1000:])
with tempfile.TemporaryDirectory(prefix='con-zfc-r11-negative-') as td:
 work=Path(td)
 for name in ['lucas_h1868','positivity']:shutil.copytree(R/name,work/name)
 p=work/'lucas_h1868/fixed/c000.signed-le.gz';raw=p.read_bytes();x=bytearray(raw);x[-1]^=1;p.write_bytes(x)
 # Corrupt compressed payload can fail decompression before hash comparison.
 q=subprocess.run([sys.executable,'-O',str(work/'lucas_h1868/check.py')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
 if q.returncode==0:raise RuntimeError('corrupt payload accepted')
 p.write_bytes(raw)
 p=work/'lucas_h1868/integer10.json';raw=p.read_bytes();d=json.loads(raw);last=d['nodes'][d['output']]
 if last['kind']!='sub':raise RuntimeError('unexpected final node')
 last['kind']='add';p.write_text(json.dumps(d))
 must_fail(work,['lucas_h1868/check.py'],'mismatch');p.write_bytes(raw)
 p=work/'positivity/sextic30.json';d=json.loads(p.read_text());d['residuals'][0]+=' + 1';p.write_text(json.dumps(d))
 must_fail(work,['positivity/check.py'],'independent literal formula')
print(json.dumps({'status':'PASS','controls':['corrupt fixed payload rejected','final norm sign mutation rejected','sextic residual mutation rejected'],'optimized_checks':True,'scope':'Rejection controls, not unbounded semantic proofs.'}))
