#!/usr/bin/env python3
"""Exercise exact historical wrappers with fake builders; never runs Lean."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[4]
BASE='Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/monitor/'
PINS={'paired.py':'b3eb4021ae3d8797adcb796bcbe3613a9363ea5b4917d85173e92e27c08f9910',
      'monitor.py':'f83085ddc84b9376d934cfbc4b29cd28b91f10a7f1ac28fd372e276b5cf542ee',
      'path_guard.py':'9af0852abe419dee3fa83a57aa8fbdb3584285c8c40a229c9ef041f610375173'}
BOOT="import runpy,sys; from pathlib import Path; p=Path(sys.argv[1]).resolve(strict=True); sys.path.insert(0,str(p.parent)); sys.argv=sys.argv[1:]; runpy.run_path(str(p),run_name='__main__')"


def need(ok,msg):
    if not ok: raise ValueError(msg)


def main():
    with tempfile.TemporaryDirectory(prefix='isolated-chain-audit-') as tmp:
        t=Path(tmp);wrap=t/'repo'/BASE;wrap.mkdir(parents=True)
        for name,digest in PINS.items():
            data=subprocess.run(['git','show','ad4cd81e5f:'+BASE+name],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
            need(hashlib.sha256(data).hexdigest()==digest, 'historical pin '+name)
            (wrap/name).write_bytes(data)
        env=dict(os.environ)
        for key in ('PYTHONOPTIMIZE','PYTHONHOME','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
            env.pop(key,None)
        site=t/'startup';site.mkdir();marker=t/'startup-ran';trace=t/'trace.jsonl'
        (site/'sitecustomize.py').write_text('import os,pathlib\npathlib.Path(os.environ["AUDIT_MARKER"]).write_text("ran")\n')
        env.update(PYTHONPATH=str(site),AUDIT_MARKER=str(marker),AUDIT_TRACE=str(trace))
        p=subprocess.run([sys.executable,'-c','print("positive")'],env=env,capture_output=True,text=True)
        need(p.returncode==0 and marker.read_text()=='ran', 'sitecustomize positive control');marker.unlink()
        for file,needle in [('paired.py','coordinator requires isolated'),('monitor.py','monitor requires isolated')]:
            childenv=env.copy();childenv.pop('PYTHONPATH')
            p=subprocess.run([sys.executable,'-B',str(wrap/file)],env=childenv,capture_output=True,text=True)
            need(p.returncode!=0 and needle in p.stderr, 'nonisolated CLI '+file+' '+p.stderr)
        opt=env|{'PYTHONOPTIMIZE':'1'}
        p=subprocess.run([sys.executable,'-I','-S','-c',BOOT,str(wrap/'paired.py')],env=opt,capture_output=True,text=True)
        need(p.returncode!=0 and 'rejects optimized' in p.stderr and not marker.exists(), 'optimized environment rejected')

        # These tiny programs are the only builders/comparators run. They
        # report flags and startup canary, then emit the toy states expected
        # by the real coordinator; no Lean binary or project input is used.
        builder=t/'fake_builder.py';builder.write_text('''import argparse,json,os,pathlib,sys\np=argparse.ArgumentParser();p.add_argument('--output',required=True);a,_=p.parse_known_args()\nout=pathlib.Path(a.output);label=out.parent.name\nwith open(os.environ['AUDIT_TRACE'],'a') as f:f.write(json.dumps({'role':label,'isolated':sys.flags.isolated,'no_site':sys.flags.no_site,'marker':pathlib.Path(os.environ['AUDIT_MARKER']).exists(),'pythonpath':os.environ.get('PYTHONPATH')})+'\\n')\nout.mkdir();(out/'state.json').write_text(json.dumps({'status':'PASS'}))\n''')
        comparator=t/'fake_comparator.py';comparator.write_text('''import json,os,pathlib,sys\nwith open(os.environ['AUDIT_TRACE'],'a') as f:f.write(json.dumps({'role':'comparator','isolated':sys.flags.isolated,'no_site':sys.flags.no_site,'marker':pathlib.Path(os.environ['AUDIT_MARKER']).exists(),'pythonpath':os.environ.get('PYTHONPATH')})+'\\n')\nprint(json.dumps({'status':'MATCHED_PASS','rows':2}))\n''')
        snap=t/'snapshot';snap.mkdir();(snap/'manifest.json').write_text('{}')
        proot=t/'provider';proot.mkdir();overlay=proot/'overlay';overlay.mkdir()
        provider=proot/'provider.json';provider.write_text(json.dumps({'root':str(proot),'overlay':str(overlay)}))
        foundation=t/'foundation.json';foundation.write_text('{}')
        digest=lambda path:hashlib.sha256(path.read_bytes()).hexdigest()
        out=t/'toy-pair'
        cmd=[sys.executable,'-I','-S','-c',BOOT,str(wrap/'paired.py'),
             '--output',str(out),'--snapshot',str(snap),'--snapshot-sha256',digest(snap/'manifest.json'),
             '--provider-receipt',str(provider),'--provider-sha256',digest(provider),'--foundation-input',str(foundation),
             '--expected-axiom-reports','0','--builder',str(builder),'--comparator',str(comparator),
             '--reserve-bytes','0','--budget-bytes','1000000','--interval','0.02','--grace','0.1']
        p=subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=20)
        need(p.returncode==0, 'toy chain failed '+p.stdout+' '+p.stderr)
        state=json.loads((out/'pair-state.json').read_text());rows=[json.loads(s) for s in trace.read_text().splitlines()]
        need(state['status']=='MATCHED_PASS' and len(state['runs'])==2, 'toy pair result')
        need([r['role'] for r in rows]==['author','peer','comparator'], 'actual child sequence')
        need(all(r['isolated']==1 and r['no_site']==1 and not r['marker'] and r['pythonpath']==str(site) for r in rows), 'child startup isolation')
        need(not marker.exists(), 'sitecustomize did not execute')
        for run in state['runs']:
            terminal=json.loads(Path(run['monitor_terminal']).read_text())
            need(terminal['outer_exit_code']==0 and terminal['command'][1:3]==['-I','-S'], 'actual monitor and child command')
        result={'status':'PASS_TOY_ISOLATED_WRAPPER_CHAIN','commit':'ad4cd81e5f','pins':PINS,
                'normal_startup_canary_exit':0,'normal_startup_canary_executed':True,
                'unisolated_cli_rejections':True,'optimized_env_rejected':True,
                'toy_coordinator_exit':p.returncode,'toy_pair_status':state['status'],
                'actual_child_rows':[{k:v for k,v in r.items() if k!='pythonpath'} for r in rows],
                'pythonpath_was_present_but_ignored':True,'monitor_child_commands_isolated':True,
                'scope':'Exact wrapper scripts with fake inputs/builders/comparator; no Lean, full preflight, real source build, or launcher verdict.'}
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
