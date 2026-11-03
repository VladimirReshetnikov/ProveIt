#!/usr/bin/env python3
"""No-Lean controls for the narrowly matched historical warning policies."""
import hashlib,importlib.util,json,shutil,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('runner',HERE/'replay.py');m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
if not __debug__:raise ValueError('optimized Python rejected')
bases=m.warning_baseline();cases={}
def check(label,fn,expect):
 try:fn();accepted=True
 except Exception:accepted=False
 if accepted!=expect:raise ValueError((label,accepted,expect))
 cases[label]=accepted
for name,rule in m.WARNING_RULES.items():
 src=Path('/tmp/example')/(name.split('.')[-1]+'.lean');text=bases[name].replace('<SOURCE>',str(src));sha=rule[0];k=name.split('.')[-1]
 check(k+' exact',lambda:m.accepted_diagnostics(name,src,sha,text,bases),True)
 check(k+' wrong module',lambda:m.accepted_diagnostics('Other',src,sha,text,bases),False)
 check(k+' wrong source sha',lambda:m.accepted_diagnostics(name,src,'0'*64,text,bases),False)
 check(k+' wrong source path',lambda:m.accepted_diagnostics(name,src,sha,text.replace(str(src),'/tmp/other.lean'),bases),False)
 check(k+' changed warning',lambda:m.accepted_diagnostics(name,src,sha,text.replace('warning:', 'warning: changed',1),bases),False)
 check(k+' extra warning',lambda:m.accepted_diagnostics(name,src,sha,text+text,bases),False)
 check(k+' extra output',lambda:m.accepted_diagnostics(name,src,sha,text+'noise\n',bases),False)
 check(k+' error',lambda:m.accepted_diagnostics(name,src,sha,text+'error: injected\n',bases),False)
 check(k+' sorryAx',lambda:m.accepted_diagnostics(name,src,sha,text+'sorryAx\n',bases),False)
with tempfile.TemporaryDirectory(prefix='warning-baseline-') as d:
 old=m.HIST;m.HIST=Path(d);shutil.copytree(old/'logs',m.HIST/'logs',ignore=lambda d,n:[x for x in n if x not in {n.replace('.','_')+'-attempt-1.log' for n in m.WARNING_RULES}]);shutil.copyfile(old/'state.json',m.HIST/'state.json')
 (m.HIST/'state.json').write_text('changed');check('historical state drift',m.warning_baseline,False);shutil.copyfile(old/'state.json',m.HIST/'state.json')
 for name in m.WARNING_RULES:
  p=m.HIST/'logs'/(name.replace('.','_')+'-attempt-1.log');p.write_text('changed');check(name+' historical log drift',m.warning_baseline,False);shutil.copyfile(old/'logs'/p.name,p)
print(json.dumps({'status':'PASS_NO_LEAN_WARNING_CONTROLS','runner_sha256':hashlib.sha256((HERE/'replay.py').read_bytes()).hexdigest(),'cases':cases,'lean_launched':False},indent=2,sort_keys=True))
