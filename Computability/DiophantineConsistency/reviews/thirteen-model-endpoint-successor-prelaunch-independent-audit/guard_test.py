#!/usr/bin/env python3
"""Exercise fail-closed startup and existing-output guards; never compile Lean."""
import json,os,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
PKG=ROOT/'Computability/DiophantineConsistency/research/thirteen-model-endpoint-successor'
env=os.environ.copy()
for k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT','PYTHONOPTIMIZE'):env.pop(k,None)
with tempfile.TemporaryDirectory(prefix='successor-guard-control-') as d:
    env['PYTHONDONTWRITEBYTECODE']='1';root=Path(d)
    launcher=PKG/'replay.py';freeze=PKG/'freeze.py'
    existing=Path(tempfile.mkdtemp(prefix='ipra-thirteen-endpoint-successor-pair-guard-',dir='/tmp'))
    link=existing.with_name(existing.name+'-link');link.symlink_to(existing,target_is_directory=True)
    controls=[('launcher_collision',[sys.executable,'-I','-S',str(launcher),'--output',str(existing)]),('launcher_symlink',[sys.executable,'-I','-S',str(launcher),'--output',str(link)]),('nonisolated',[sys.executable,str(launcher),'--output','/tmp/not-a-successor']),('optimized',[sys.executable,'-I','-S','-O',str(launcher),'--output','/tmp/not-a-successor']),('collision',[sys.executable,'-I','-S',str(freeze),'--output','/tmp/ipra-thirteen-endpoint-source-01'])]
    result=[]
    for name,cmd in controls:
        p=subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=30)
        if p.returncode==0:raise ValueError('unexpected success '+name)
        expected={'launcher_collision':'output exists','launcher_symlink':'output exists','nonisolated':'invoke with python3 -I -S','optimized':'optimized Python rejected','collision':'output exists'}[name]
        if expected not in p.stderr:raise ValueError((name,p.returncode,p.stderr))
        result.append({'case':name,'exit':p.returncode})
    link.unlink();existing.rmdir()
    print(json.dumps({'status':'PASS_SUCCESSOR_STARTUP_GUARDS','controls':result,'scope':'Initial guard rejection only; no Lean build.'},indent=2))
