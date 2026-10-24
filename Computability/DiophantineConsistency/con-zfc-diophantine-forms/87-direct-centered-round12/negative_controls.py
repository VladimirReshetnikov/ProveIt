#!/usr/bin/env python3
"""Selected mutations must fail for a mathematical/data reason, not missing files."""
from pathlib import Path
import gzip,json,shutil,subprocess,sys,tempfile
R=Path(__file__).resolve().parent;results=[]
with tempfile.TemporaryDirectory(prefix='round12-mutations-') as td:
 T=Path(td)/'packet';shutil.copytree(R,T,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
 def case(name,path,mutator,command):
  p=T/path;original=p.read_bytes();mutator(p);r=subprocess.run([sys.executable,*command],cwd=T,capture_output=True,text=True);p.write_bytes(original)
  if r.returncode==0:raise ValueError('accepted mutation '+name)
  out=r.stdout+r.stderr
  if any(s in out for s in ['FileNotFoundError','ModuleNotFoundError','SyntaxError']):raise ValueError('invalid negative control '+name+' '+out)
  if not any(s in out for s in ['ValueError','RuntimeError']):raise ValueError('unexplained negative control '+name+' '+out)
  results.append({'case':name,'rejected':True,'reason':out.strip().splitlines()[-1]})
 def jsonchange(fn):
  def run(p):
   j=json.loads(p.read_text());fn(j);p.write_text(json.dumps(j))
  return run
 case('norm operation corruption','norm/integer10_center2.json',jsonchange(lambda j:j['nodes'][j['output']].__setitem__('kind','add')),['norm_audit/check_independent.py'])
 case('fixed numeral corruption','norm/fixed/c000.signed-le.gz',lambda p:p.write_bytes(gzip.compress(gzip.decompress(p.read_bytes())+b'\x01',mtime=0)),['norm_audit/check_independent.py'])
 case('positive finalizer corruption','positive/p11_degree211.json',jsonchange(lambda j:j['source'][-1].__setitem__(1,'-')),['small_audit/check.py'])
 case('low degree metric corruption','low_degree/integer21_degree16.json',jsonchange(lambda j:j.__setitem__('exact_degree',18)),['small_audit/check.py'])
 case('short guard top coordinate corruption','source/short_guard/layout.json',jsonchange(lambda j:j['weights'].__setitem__(0,0)),['source/short_guard/check.py'])
print(json.dumps({'status':'PASS','controls':results},indent=2))
