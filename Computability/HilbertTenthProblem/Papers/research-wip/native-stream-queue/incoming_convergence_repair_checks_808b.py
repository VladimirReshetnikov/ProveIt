"""Portable source-pinned private repair replay for two incoming 808b reports."""
from pathlib import Path
from contextlib import contextmanager
from collections import Counter
from fractions import Fraction as F
import argparse,copy,hashlib,importlib.util,json,shutil,subprocess,sys,tempfile
PINS={
 'bellman_generator':'5a5b20f384afb64f9a408dcd7a86f1e9c27dabfb9fcf9401540d479512391397',
 'bellman_checker':'44ed5e089bd4e42ae4bf665d816fd92c1fb067cb6778702f7b36391d61230aec',
 'quadratic_compiler':'a6894f6c3da3ee8c3bce24875d34bd9df4b2d77546f162bf63a5648d618cebef',
 'bellman_patch':'697c2864262e9cc71dccf228aeba6b34c93140653846af496c0abcbbb513bb04',
 'quadratic_patch':'79f86b626d7d067117ad010b63bcf2c7f3113b7caa43ae15cc7f01051988c77d',
 'patched_bellman_checker':'349fc50d5eb8d62287037e4116d95a18d48a8db1a2dde17d1211200febf20ce0',
 'patched_quadratic_compiler':'85dca2b8a53492a4193bd0da44bfaf228d14a00ddb1ab6d21927f40746306841'}
def pin(path,key):
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==PINS[key],key
@contextmanager
def modules(paths):
 missing=object();saved={};made={}
 try:
  for name,path in paths:
   saved[name]=sys.modules.get(name,missing);spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec);sys.modules[name]=module;spec.loader.exec_module(module);made[name]=module
  yield made
 finally:
  for name,old in saved.items():
   if old is missing:sys.modules.pop(name,None)
   else:sys.modules[name]=old

def verify(bellman_root,quadratic_root,bellman_patch,quadratic_patch):
 if not __debug__:raise RuntimeError('Assertions are required')
 bellman_root,quadratic_root,bellman_patch,quadratic_patch=map(Path,(bellman_root,quadratic_root,bellman_patch,quadratic_patch))
 pin(bellman_root/'code/bellman_diophantine.py','bellman_generator');pin(bellman_root/'code/check_certificate.py','bellman_checker');pin(quadratic_root/'code/quadratic_compiler.py','quadratic_compiler');pin(bellman_patch,'bellman_patch');pin(quadratic_patch,'quadratic_patch')
 counts=Counter()
 def check(ok,label):assert ok,label;counts[label]+=1
 def reject(fn,label):
  try:fn()
  except (ValueError,TypeError,AssertionError,KeyError,IndexError):counts[label]+=1
  else:raise AssertionError(label)
 with tempfile.TemporaryDirectory(prefix='incoming808-repairs-') as temporary:
  scratch=Path(temporary);B=scratch/'bellman';Q=scratch/'quadratic'
  for source,dest,patch in [(bellman_root,B,bellman_patch),(quadratic_root,Q,quadratic_patch)]:
   shutil.copytree(source,dest,ignore=shutil.ignore_patterns('__pycache__'))
   done=subprocess.run(['patch','--batch','--fuzz=0','-p1','-i',str(patch.resolve())],cwd=dest,capture_output=True,text=True,timeout=300);assert done.returncode==0,(done.stdout,done.stderr)
  pin(B/'code/check_certificate.py','patched_bellman_checker');pin(Q/'code/quadratic_compiler.py','patched_quadratic_compiler')
  paths=[('_repair808_generator',B/'code/bellman_diophantine.py'),('_repair808_checker',B/'code/check_certificate.py'),('_repair808_quadratic',Q/'code/quadratic_compiler.py')]
  with modules(paths) as loaded:
   bell,bc,quad=(loaded[n] for n,p in paths)
   game=bell.Game(('lin','lin'),((((0,F(1)),),),(((1,F(1)),),)));g=game.export();g.update(initial_terminal_payoffs=['0','0'],observed_pair=[0,1])
   q=bell.certificate(game,[0,0],1,(0,1));cp=scratch/'certificate.json';gp=scratch/'game.json';q.export(cp);valid=json.loads(cp.read_text())
   def call(data=valid,external=g):
    cp.write_text(json.dumps(data));gp.write_text(json.dumps(external));return bc.check(cp,gp)
   check(call()['polynomial_value']==0,'bellman_valid_baseline')
   forged=copy.deepcopy(valid);forged['metadata']['input_numerators']=[1,0];external=copy.deepcopy(g);external['initial_terminal_payoffs']=['1','0'];reject(lambda:call(forged,external),'bellman_original_false_input_rejected')
   for field in ['states','binary_states','horizon','probability_denominator','step_denominator','discount_numerator','initial_denominator','witness_scale','witnesses','squares','products','endpoint_squares','degree_at_most']:
    for bad in [True,1.0,-1,valid['metadata'][field]+1]:
     data=copy.deepcopy(valid);data['metadata'][field]=bad;reject(lambda data=data:call(data),'bellman_metadata_rejections')
   for field in ['input_numerators','initial_numerators']:
    for bad in [[1,0],[False,0],[0.0,0],[0],[0,0,0]]:
     data=copy.deepcopy(valid);data['metadata'][field]=bad;reject(lambda data=data:call(data),'bellman_vector_rejections')
   for field,bad in [('observed_pair',[False,1]),('observed_pair',[0.0,1]),('observed_pair',[0,2]),('observed_pair',[1,0]),('terminal_mode','other'),('target','1'),('common_reward','1/3'),('common_reward',False),('common_reward',0.0)]:
    data=copy.deepcopy(valid);data['metadata'][field]=bad;reject(lambda data=data:call(data),'bellman_metadata_rejections')
   for field,bad in [('format','other'),('states',True),('states',2.0),('states',3),('owners',['min','lin']),('owners',['other','lin']),('owners',['lin']),('discount','2/3'),('common_reward','1/7'),('common_uniform_reset','1'),('common_uniform_reset',0.5),('initial_terminal_payoffs',['1','0']),('observed_pair',[1,0]),('observed_pair',[False,1])]:
    data=copy.deepcopy(g);data[field]=bad;reject(lambda data=data:call(valid,data),'bellman_game_rejections')
   for action in [[[True,'1']],[[0.0,'1']],[[2,'1']],[[0,'1/2']],[[0,'1/2'],[0,'1/2']],[[0,'-1/4'],[1,'5/4']],[[0,True]],[[0,1.0]]]:
    data=copy.deepcopy(g);data['base_actions'][0][0]=action;reject(lambda data=data:call(valid,data),'bellman_game_rejections')
   for bad in [-2,False,-1.0]:
    data=copy.deepcopy(valid);data['constant_index']=bad;reject(lambda data=data:call(data),'bellman_polynomial_schema_rejections')
   for bad in [True,0.0,-1]:
    data=copy.deepcopy(valid);data['assignment'][0]=bad;reject(lambda data=data:call(data),'bellman_polynomial_schema_rejections')
   for mode in ['pair','consensus','point']:
    for T in [0,1,3]:
     for A,den in [([0,0],1),([1,2],3),([10**100,0],10**100+1)]:
      gg=bell.Game(('min','max'),((((0,F(1)),),((1,F(1)),)),(((1,F(1)),),((0,F(1)),))),F(1,3),F(2,3),F(1,7))
      qq=bell.certificate(gg,A,T,(0,1),den,target=F(3,7) if mode=='point' else None,consensus=mode=='consensus');qq.export(cp);d=json.loads(cp.read_text());ge=gg.export();ge['initial_terminal_payoffs']=[str(F(x,den)) for x in A]
      result=call(d,ge);check(result['polynomial_value']==qq.evaluate(),'bellman_valid_general_scalings')
   for name in ['small','countdown','fixedpoint']:
    result=bc.check(B/f'artifacts/{name}_certificate.json',B/f'artifacts/{name}_game.json');check(result['polynomial_value']==0,'bellman_delivered_certificates')
   # Deep caller snapshots at rule, network and export boundaries.
   head=[1,1];literal=[0,1];tail=[literal];r=quad.Rule(head,tail);seed=[0,1];seeds=[seed];rules=[r];net=quad.Network(2,2,seeds,rules);c=quad.Compiled(net,False);w,labels,times=c.witness();baseline=c.c.export(w)
   head[0]=0;literal[1]=2;tail.clear();seed[1]=2;seeds.clear();rules.clear()
   check(net.seeds==((0,1),) and net.rules==(quad.Rule((1,1),((0,1),)),),'quadratic_deep_input_snapshots')
   check(c.witness()==(w,labels,times) and c.c.evaluate(w)==0,'quadratic_snapshot_semantics')
   for key in ['parameters','witnesses','assignment','affine_residuals','nonnegative_products','expanded_polynomial','counts']:
    ex=c.c.export(w);ex[key].clear();check(c.c.export(w)==baseline,'quadratic_deep_export_snapshots')
   for bad in [True,False,1.5,-1,'1']:
    for field in ['sites','labels']:
     args=dict(sites=2,labels=2,seeds=(),rules=());args[field]=bad;reject(lambda args=args:quad.Compiled(quad.Network(**args)),'quadratic_exact_schema_rejections')
    for literal in [(bad,1),(0,bad)]:
     reject(lambda literal=literal:quad.Compiled(quad.Network(2,2,(literal,),())),'quadratic_exact_schema_rejections')
     reject(lambda literal=literal:quad.Rule(literal,()),'quadratic_exact_schema_rejections')
   for bad in [True,False,0,-1,1.5]:
    net=quad.Network(1,1,(),(quad.Rule((0,1),()),));reject(lambda bad=bad:quad.simulate(net,[bad]),'quadratic_exact_delay_rejections')
   for bad in [1,0,'yes',None]:
    net=quad.Network(1,1,(),());reject(lambda bad=bad:quad.Compiled(net,bad),'quadratic_timed_option_rejections');reject(lambda bad=bad:quad.HornCompiled(net,bad),'quadratic_timed_option_rejections')
   for bad in [True,0.0,-1]:
    x=dict(w);x[next(iter(x))]=bad;reject(lambda x=x:c.c.evaluate(x),'quadratic_natural_assignment_rejections')
  # Complete author suites run in private patched packages only.
  for directory,command,label in [(B,['code/run_checks.py'],'bellman'),(Q,['code/test_compiler.py'],'quadratic'),(Q,['code/verify_exports.py'],'quadratic_exports')]:
   done=subprocess.run([sys.executable]+command,cwd=directory,check=True,capture_output=True,text=True,timeout=240);counts['repaired_original_author_suites']+=1
  for source,dest,folder,receipt in [(bellman_root,B,'artifacts','verification.json'),(quadratic_root,Q,'results','test_receipt.json')]:
   for file in (source/folder).glob('*.json'):
    if file.name in ['pdf_preflight.json','export_verification.json',receipt]:continue
    check(file.read_bytes()==(dest/folder/file.name).read_bytes(),'byte_identical_valid_exports')
   old=json.loads((source/folder/receipt).read_text());new=json.loads((dest/folder/receipt).read_text())
   for key in ['python','runtime_seconds']:old.pop(key,None);new.pop(key,None)
   check(old==new,'unchanged_normalized_author_receipts')
 return {'status':'PASS','pins':PINS,'counts':dict(counts),'scope':'Private exact-source patch application; input binding and immutable exact-natural descriptor repair. Valid emitted polynomials unchanged.'}

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--bellman-root',required=True);p.add_argument('--quadratic-root',required=True);p.add_argument('--bellman-patch',required=True);p.add_argument('--quadratic-patch',required=True);p.add_argument('--output');a=p.parse_args();result=verify(a.bellman_root,a.quadratic_root,a.bellman_patch,a.quadratic_patch);raw=json.dumps(result,indent=2)+'\n'
 if a.output:Path(a.output).write_text(raw)
 print(raw,end='')
