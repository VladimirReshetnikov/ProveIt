#!/usr/bin/env python3
"""Mutation-test the exact held v6 three-baseline policy function."""
import ast,json,re
from hashlib import sha256
from pathlib import Path
H=Path(__file__).resolve().parent;runner=H/'run-v6.py'
paths=[H/'warning-baseline-pigeonhole/baseline.txt',H/'warning-baseline-modelarithmetic/baseline.txt',H/'warning-baseline-ratiobounds/baseline.txt']
tree=ast.parse(runner.read_text());func=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='diagnostics_allowed']
keys={'WARNING_MODULE','WARNING_SOURCE','MODEL_WARNING_MODULE','MODEL_WARNING_SOURCE','RATIO_WARNING_MODULE','RATIO_WARNING_SOURCE'};names={}
for n in tree.body:
 if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id in keys:names[n.targets[0].id]=ast.literal_eval(n.value)
if len(func)!=1 or set(names)!=keys:raise RuntimeError('missing policy components')
env={'re':re,**names};exec(compile(ast.Module(body=func,type_ignores=[]),str(runner),'exec'),env);f=env['diagnostics_allowed']
modules=[names['WARNING_MODULE'],names['MODEL_WARNING_MODULE'],names['RATIO_WARNING_MODULE']]
sources=[names['WARNING_SOURCE'],names['MODEL_WARNING_SOURCE'],names['RATIO_WARNING_SOURCE']]
baselines=[p.read_text() for p in paths];path='/tmp/example/source.lean';logs=[b.replace('<SOURCE>',path) for b in baselines];tests={}
for i in range(3):
 tests[f'exact_{i}']=f(modules[i],sources[i],logs[i],path,*baselines)
 tests[f'wrong_hash_{i}']=f(modules[i],'wrong',logs[i],path,*baselines)
 tests[f'changed_log_{i}']=f(modules[i],sources[i],logs[i]+'extra\n',path,*baselines)
 tests[f'coded_warning_{i}']=f(modules[i],sources[i],logs[i]+'warning(lean.extra): x\n',path,*baselines)
 tests[f'coded_error_{i}']=f(modules[i],sources[i],logs[i]+'error(lean.extra): x\n',path,*baselines)
 tests[f'sorry_{i}']=f(modules[i],sources[i],logs[i]+'sorryAx\n',path,*baselines)
 for j in range(3):
  if i!=j:tests[f'cross_{i}_{j}']=f(modules[i],sources[i],logs[j],path,*baselines)
tests['clean_other']=f('Other','other','clean',path,*baselines)
tests['unrelated_warning']=f('Other','other','warning: x',path,*baselines)
expected={k:(k.startswith('exact_') or k=='clean_other') for k in tests}
if tests!=expected:raise RuntimeError('policy mutation failed: '+repr(tests))
print(json.dumps({'status':'PASS','runner_sha256':sha256(runner.read_bytes()).hexdigest(),
 'baseline_sha256':[sha256(p.read_bytes()).hexdigest() for p in paths],'tests':tests},sort_keys=True))
