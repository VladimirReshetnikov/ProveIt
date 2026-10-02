"""Portable exact-integer/Fraction scale regression and private author replay."""
from pathlib import Path
from contextlib import contextmanager
from collections import Counter
from fractions import Fraction as F
import argparse,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
PINS={'original_generator':'5a5b20f384afb64f9a408dcd7a86f1e9c27dabfb9fcf9401540d479512391397',
 'patch':'27879a31d4b574d962a22044a09a005045d5f0a182f4786f891951d677254f25',
 'patched_generator':'5ac8bbee279140e68d591874a10a00221799c9c2f94d154b6396c966993cf706'}
def pin(path,key):assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==PINS[key],key
@contextmanager
def modules(paths):
 missing=object();saved={};made={}
 try:
  for name,path in paths:
   saved[name]=sys.modules.get(name,missing);s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);sys.modules[name]=m;s.loader.exec_module(m);made[name]=m
  yield made
 finally:
  for name,old in saved.items():
   if old is missing:sys.modules.pop(name,None)
   else:sys.modules[name]=old

def verify(bellman_root,scale_patch):
 if not __debug__:raise RuntimeError('Assertions are required')
 bellman_root,scale_patch=Path(bellman_root),Path(scale_patch);pin(bellman_root/'code/bellman_diophantine.py','original_generator');pin(scale_patch,'patch');counts=Counter()
 def check(ok,label):assert ok,label;counts[label]+=1
 def reject(fn):
  try:fn()
  except ValueError:counts['invalid_scale_rejections']+=1
  else:raise AssertionError('invalid scale accepted')
 with tempfile.TemporaryDirectory(prefix='incoming808-scale-') as temp:
  work=Path(temp)/'package';shutil.copytree(bellman_root,work,ignore=shutil.ignore_patterns('__pycache__'))
  done=subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(scale_patch.resolve())],cwd=work,capture_output=True,text=True,timeout=300);assert done.returncode==0,(done.stdout,done.stderr);pin(work/'code/bellman_diophantine.py','patched_generator')
  paths=[('_scale808_original',bellman_root/'code/bellman_diophantine.py'),('_scale808_repaired',work/'code/bellman_diophantine.py')]
  with modules(paths) as loaded:
   old,new=(loaded[name] for name,path in paths);p=old.Program(1,(old.Instruction('halt'),))
   bad=p.encode(0,[1075],scale=1);good=p.encode(0,[1075]);check(type(bad[-1]) is float and bad[-1]==0.0 and good[-1]==F(1,2**1075),'original_integer_scale_underflow_reproduced')
   p=new.Program(1,(new.Instruction('halt'),))
   for n in [0,1,52,53,1023,1074,1075,2048,4096]:
    for scale in [1,2,10**99,10**99+7,F(3,7),F(1,2**100)]:
     result=p.encode(0,[n],scale=scale);expected=[F(scale),F(scale),F(scale)/2**n]
     check(result==expected and all(type(x) is F for x in result),'exact_large_scale_counter_encodings')
     check(result==p.encode(0,[n],scale=F(scale)),'integer_fraction_scale_equivalence')
   for scale in [True,False,0.5,1.0,float('inf'),float('nan'),None,'1',0,-1,F(0),F(-1,7)]:reject(lambda scale=scale:p.encode(0,[1075],scale=scale))
   for operation in ['inc','dec']:
    p=new.Program(1,(new.Instruction(operation,0,0,1),new.Instruction('halt')));c=new.counter_circuit(p)
    for n in [0,1,1075,2048]:
     for scale in [1,10**99+7,F(3,7)]:
      actual=c.apply(p.encode(0,[n],scale=scale));state=1 if operation=='dec' and n==0 else 0;value=n+1 if operation=='inc' else max(0,n-1)
      check(actual==p.encode(state,[value],scale=F(scale)),'scaled_native_counter_steps')
  done=subprocess.run([sys.executable,'code/run_checks.py'],cwd=work,capture_output=True,text=True,check=True,timeout=300);new_receipt=json.loads((work/'artifacts/verification.json').read_text());check(new_receipt['total_assertions']==26077,'full_author_suite')
  for original in (bellman_root/'artifacts').glob('*.json'):
   if original.name in ['verification.json','pdf_preflight.json']:continue
   check(original.read_bytes()==(work/'artifacts'/original.name).read_bytes(),'byte_identical_valid_exports')
  original=json.loads((bellman_root/'artifacts/verification.json').read_text());original.pop('python');new_receipt.pop('python');check(original==new_receipt,'unchanged_normalized_author_receipt')
 return {'status':'PASS','pins':PINS,'counts':dict(counts),'scope':'Exact loader scale boundary only; default/Fraction paths and every delivered polynomial remain unchanged.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--bellman-root',required=True);p.add_argument('--scale-patch',required=True);p.add_argument('--output');a=p.parse_args();result=verify(a.bellman_root,a.scale_patch);raw=json.dumps(result,indent=2)+'\n'
 if a.output:Path(a.output).write_text(raw)
 print(raw,end='')
