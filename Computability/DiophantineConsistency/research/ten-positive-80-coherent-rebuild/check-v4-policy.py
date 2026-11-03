#!/usr/bin/env python3
"""Mutation-test the exact function used by the held v4 runner."""
import ast,json,re
from hashlib import sha256
from pathlib import Path
H=Path(__file__).resolve().parent;runner=H/'run-v4.py';base=H/'warning-baseline-pigeonhole/baseline.txt'
tree=ast.parse(runner.read_text());func=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='diagnostics_allowed']
if len(func)!=1:raise RuntimeError('missing unique policy function')
names={}
for node in tree.body:
 if isinstance(node,ast.Assign) and len(node.targets)==1 and isinstance(node.targets[0],ast.Name) and node.targets[0].id in ('WARNING_MODULE','WARNING_SOURCE'):
  names[node.targets[0].id]=ast.literal_eval(node.value)
if len(names)!=2:raise RuntimeError('missing policy constants')
env={'re':re,**names};exec(compile(ast.Module(body=func,type_ignores=[]),str(runner),'exec'),env)
f=env['diagnostics_allowed'];module=names['WARNING_MODULE'];source=names['WARNING_SOURCE'];baseline=base.read_text();path='/tmp/example/ArithmeticPellPigeonhole.lean';log=baseline.replace('<SOURCE>',path)
tests={'exact':f(module,source,log,path,baseline),
       'clean_other':f('Other','other','clean',path,baseline),
       'wrong_module':f('Other',source,log,path,baseline),
       'wrong_source':f(module,'other',log,path,baseline),
       'changed_line':f(module,source,log.replace(':40:4:',':40:5:',1),path,baseline),
       'extra_coded_warning':f(module,source,log+'warning(lean.extra): extra\n',path,baseline),
       'extra_coded_error':f(module,source,log+'error(lean.extra): extra\n',path,baseline),
       'extra_sorry':f(module,source,log+'sorryAx\n',path,baseline),
       'other_warning':f('Other','other','warning: extra',path,baseline),
       'other_coded_error':f('Other','other','error(lean.foo): failed',path,baseline)}
expected={'exact':True,'clean_other':True,**{k:False for k in tests if k not in ('exact','clean_other')}}
if tests!=expected:raise RuntimeError('policy mutation failed: '+repr(tests))
print(json.dumps({'status':'PASS','runner_sha256':sha256(runner.read_bytes()).hexdigest(),
                  'baseline_sha256':sha256(base.read_bytes()).hexdigest(),'tests':tests},sort_keys=True))
