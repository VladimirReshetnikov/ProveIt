#!/usr/bin/env python3
"""Mutation-test the actual held v5 two-baseline policy function."""
import ast,json,re
from hashlib import sha256
from pathlib import Path
H=Path(__file__).resolve().parent;runner=H/'run-v5.py';base=H/'warning-baseline-pigeonhole/baseline.txt';model=H/'warning-baseline-modelarithmetic/baseline.txt'
tree=ast.parse(runner.read_text());func=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='diagnostics_allowed']
if len(func)!=1:raise RuntimeError('missing policy function')
keys={'WARNING_MODULE','WARNING_SOURCE','MODEL_WARNING_MODULE','MODEL_WARNING_SOURCE'};names={}
for n in tree.body:
 if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in keys:names[n.targets[0].id]=ast.literal_eval(n.value)
if set(names)!=keys:raise RuntimeError('missing policy constants')
env={'re':re,**names};exec(compile(ast.Module(body=func,type_ignores=[]),str(runner),'exec'),env)
f=env['diagnostics_allowed'];p=base.read_text();m=model.read_text();path='/tmp/example/source.lean';pl=p.replace('<SOURCE>',path);ml=m.replace('<SOURCE>',path)
a=names['WARNING_MODULE'];ah=names['WARNING_SOURCE'];b=names['MODEL_WARNING_MODULE'];bh=names['MODEL_WARNING_SOURCE']
tests={'pigeonhole_exact':f(a,ah,pl,path,p,m),'model_exact':f(b,bh,ml,path,p,m),'clean_other':f('Other','other','clean',path,p,m),
 'cross_module_p':f(b,ah,pl,path,p,m),'cross_module_m':f(a,bh,ml,path,p,m),
 'wrong_hash_p':f(a,'other',pl,path,p,m),'wrong_hash_m':f(b,'other',ml,path,p,m),
 'changed_p':f(a,ah,pl.replace(':40:4:',':40:5:',1),path,p,m),'changed_m':f(b,bh,ml.replace(':90:18:',':90:19:',1),path,p,m),
 'added_coded_warning':f(b,bh,ml+'warning(lean.extra): extra\n',path,p,m),
 'added_coded_error':f(a,ah,pl+'error(lean.extra): extra\n',path,p,m),
 'added_sorry':f(b,bh,ml+'sorryAx\n',path,p,m),'unrelated_warning':f('Other','other','warning: x',path,p,m)}
allow={'pigeonhole_exact','model_exact','clean_other'};expected={k:k in allow for k in tests}
if tests!=expected:raise RuntimeError('policy mutation failed: '+repr(tests))
print(json.dumps({'status':'PASS','runner_sha256':sha256(runner.read_bytes()).hexdigest(),
                  'baseline_sha256':[sha256(base.read_bytes()).hexdigest(),sha256(model.read_bytes()).hexdigest()],
                  'tests':tests},sort_keys=True))
