#!/usr/bin/env python3
"""Read-only preflight and actual fake-child review; never launch a build."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[4]
HERE=ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay'
PINS={'launch.py':'6e3df86b8218a759612992a41f5dbef84bce0cc5e9ecc19e6ffeeda84d3343c5',
      'gates.py':'76f153b8be70b4c804469934c2dcaf92f9803f0024932a48674c96d3b47d373e',
      'test_gates.py':'4294b614a0ba6253a5655f0e1a43c2a396d6e7ee12fb7c50dc2d58740207c494',
      'test_launch.py':'d4575af81c45470c9984de71cabbde08cec2f6a11455367ea9fff8ea946aba29'}


def need(ok,msg):
    if not ok:raise ValueError(msg)


def main():
    for name,h in PINS.items():
        data=(HERE/name).read_bytes()
        hist=subprocess.run(['git','show','face1a63cd:'+(HERE/name).relative_to(ROOT).as_posix()],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(data==hist and hashlib.sha256(data).hexdigest()==h,'exact historical source '+name)
    clean=dict(os.environ)
    for key in list(clean):
        if key.startswith('PYTHON') or key in ('LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT'):
            clean.pop(key,None)
    observed={}
    outputs=[Path('/tmp/ipra-ordinary12-coexistence-pair-01'),Path('/tmp/ipra-ordinary12-coexistence-preflight-01.json'),Path('/tmp/ipra-ordinary12-coexistence-launch-terminal-01.json')]
    need(not any(os.path.lexists(p) for p in outputs),'real output occupied before review')
    for name in ('test_gates.py','test_launch.py'):
        p=subprocess.run([sys.executable,'-B',str(HERE/name)],cwd=ROOT,env=clean,capture_output=True,text=True,timeout=30)
        need(p.returncode==0 and 'PASS_' in p.stdout,'toy tests '+name+' '+p.stderr)
        observed[name]={'exit':p.returncode,'stdout':p.stdout.strip()}
    for label,flags,extra,needle in [
        ('nonisolated',[],{},'invoke launcher as'),('isolated_without_no_site',['-I'],{},'invoke launcher as'),
        ('no_site_without_isolated',['-S'],{},'invoke launcher as'),
        ('optimized_O',['-I','-S','-O'],{},'rejects optimized'),
        ('optimized_OO',['-I','-S','-OO'],{},'rejects optimized'),
        ('optimized_env',['-I','-S'],{'PYTHONOPTIMIZE':'1'},'rejects optimized')]:
        p=subprocess.run([sys.executable,'-B',*flags,str(HERE/'launch.py')],env=clean|extra,capture_output=True,text=True)
        need(p.returncode!=0 and needle in p.stderr and not p.stdout,'entry guard '+label)
        observed[label]={'exit':p.returncode,'stderr_last_line':p.stderr.strip().splitlines()[-1]}

    # Directly invoke only preflight, in isolated mode: main() and pair launch
    # are not called. The real-source/provider check is strictly read-only.
    code='''import importlib.util,json,pathlib,sys\np=pathlib.Path(sys.argv[1]);s=importlib.util.spec_from_file_location("audit_launch",p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);x=m.preflight();print(json.dumps({"status":x["status"],"source":x["source"],"provider":x["provider"],"reviews":len(x["reviews"]),"free_disk_bytes":x["free_disk_bytes"]}))'''
    p=subprocess.run([sys.executable,'-I','-S','-B','-c',code,str(HERE/'launch.py')],cwd=ROOT,env=clean,capture_output=True,text=True,timeout=120)
    need(p.returncode==0,'read-only preflight '+p.stderr); pre=json.loads(p.stdout)
    need(pre['status']=='PASS_PINNED_COEXISTENCE_PREFLIGHT' and pre['source']['project_modules']==70 and
         pre['provider']['foundation_artifacts']==1540 and pre['provider']['guard_paths']==14764 and pre['reviews']==6,
         'preflight counts')
    observed['live_readonly_preflight']={'exit':p.returncode,'result':pre}

    with tempfile.TemporaryDirectory(prefix='outer-launcher-audit-') as td:
        t=Path(td);site=t/'site';site.mkdir();marker=t/'marker'; fake=t/'fake';fake.mkdir()
        (site/'sitecustomize.py').write_text('import os,pathlib\npathlib.Path(os.environ["AUDIT_MARKER"]).write_text("ran")\n')
        env=clean|{'PYTHONPATH':str(site),'AUDIT_MARKER':str(marker),'LEAN_PATH':'AUDIT_LEAN'}
        p=subprocess.run([sys.executable,'-c','print("positive")'],env=env,capture_output=True,text=True)
        need(p.returncode==0 and marker.read_text()=='ran','startup positive control');marker.unlink()
        p=subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'launch.py'),'unexpected'],env=env,capture_output=True,text=True)
        need(p.returncode!=0 and 'takes no arguments' in p.stderr and not marker.exists(), 'isolated parent startup')
        (fake/'path_guard.py').write_text('VALUE="AUDIT_FAKE_WRAPPER"\n')
        (fake/'paired.py').write_text('''import json,os,pathlib,sys,path_guard\nkeys=['PYTHONPATH','PYTHONHOME','PYTHONSTARTUP','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT','PYTHONNOUSERSITE']\nprint(json.dumps({'isolated':sys.flags.isolated,'no_site':sys.flags.no_site,'marker':pathlib.Path(os.environ['AUDIT_MARKER']).exists(),'wrapper':path_guard.VALUE,'env':{k:os.environ.get(k) for k in keys}}))\nsys.exit(int(os.environ['AUDIT_CHILD_EXIT']))\n''')
        # This isolated harness imports exact launcher bytes, substitutes only
        # its preflight and output paths, and lets its genuine Popen run a
        # harmless fake coordinator. Neither 70-source builder is accessible.
        harness='''import importlib.util,os,pathlib,sys\np=pathlib.Path(sys.argv[1]);root=pathlib.Path(sys.argv[2]);s=importlib.util.spec_from_file_location("audit_launch",p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)\nm.MON=root/"fake";m.OUTPUT=root/("pair-"+os.environ["AUDIT_CHILD_EXIT"]);m.PREFLIGHT=root/("pre-"+os.environ["AUDIT_CHILD_EXIT"]+".json");m.TERMINAL=root/("terminal-"+os.environ["AUDIT_CHILD_EXIT"]+".json");m.preflight=lambda:{"status":"TOY_ONLY"}\nfor k in ("PYTHONHOME","PYTHONSTARTUP","LEAN_SRC_PATH","LEAN_SYSROOT","LD_LIBRARY_PATH","LD_PRELOAD","LD_AUDIT"):os.environ[k]="AUDIT_REMOVE"\nsys.argv=[str(p)];raise SystemExit(m.main())'''
        for child_exit in (0,7):
            childenv=env|{'AUDIT_CHILD_EXIT':str(child_exit)}
            p=subprocess.run([sys.executable,'-I','-S','-B','-c',harness,str(HERE/'launch.py'),str(t)],env=childenv,capture_output=True,text=True,timeout=20)
            need(p.returncode==child_exit,'fake child propagated '+str(child_exit)+' '+p.stderr)
            terminal=json.loads((t/('terminal-'+str(child_exit)+'.json')).read_text())
            child=json.loads(terminal['stdout'])
            need(terminal['outer_exit_code']==child_exit and terminal['command'][1:4]==['-I','-S','-c'], 'recorded child')
            need(child['isolated']==child['no_site']==1 and not child['marker'] and child['wrapper']=='AUDIT_FAKE_WRAPPER','isolated bootstrap')
            for key,value in child['env'].items():
                need(value==('1' if key=='PYTHONNOUSERSITE' else None),'child env '+key)
            need(not marker.exists(), 'sitecustomize executed')
            observed['fake_child_'+str(child_exit)]={'launcher_exit':p.returncode,'recorded_child_exit':terminal['outer_exit_code'],
                 'isolated':child['isolated'],'no_site':child['no_site'],'startup_canary':child['marker'],
                 'named_variables_scrubbed':True,'local_wrapper_import':child['wrapper']}
    need(not any(os.path.lexists(p) for p in outputs),'real output created by audit')
    print(json.dumps({'status':'PASS_INDEPENDENT_ISOLATED_LAUNCHER_AUDIT','reviewed_commit':'face1a63cd','pins':PINS,
       'observed':observed,'real_output_paths_untouched':True,
       'scope':'Read-only point-in-time preflight and isolated fake children; no real build, no guarantee of race-free inputs or hard resource quotas, and no graph transport or iPRA theorem.'},indent=2))


if __name__=='__main__':main()
