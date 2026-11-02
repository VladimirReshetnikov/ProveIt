#!/usr/bin/env python3
"""No-build audit of the historical pinned coexistence launcher."""
import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[4]
HERE = ROOT/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/difference-ring-build-plan/coherent-replay'
PINS = {'launch.py':'d965a46a57bdea680fe8e4e6d3be0852bd44e8ce84c7861618a8fda92eb9e0f1',
        'gates.py':'76f153b8be70b4c804469934c2dcaf92f9803f0024932a48674c96d3b47d373e',
        'test_gates.py':'4294b614a0ba6253a5655f0e1a43c2a396d6e7ee12fb7c50dc2d58740207c494',
        'test_launch.py':'b7c751e2ef2764a8a6420472eda1eb06837321dd4358c52063eb86048bb0f9cf'}


def need(ok, msg):
    if not ok: raise ValueError(msg)


def main():
    snapshot=tempfile.TemporaryDirectory(prefix='launcher-historical-snapshot-')
    here=Path(snapshot.name)/HERE.relative_to(ROOT)
    here.mkdir(parents=True)
    for name,digest in PINS.items():
        rev='2b44686e4b:'+(HERE/name).relative_to(ROOT).as_posix()
        historical=subprocess.run(['git','show',rev],cwd=ROOT,stdout=subprocess.PIPE,check=True).stdout
        need(hashlib.sha256(historical).hexdigest()==digest, 'historical pin '+name)
        (here/name).write_bytes(historical)
    clean=dict(os.environ)
    for name in ('PYTHONPATH','PYTHONHOME','PYTHONOPTIMIZE','LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):
        clean.pop(name,None)
    observed={}
    for filename in ('test_gates.py','test_launch.py'):
        p=subprocess.run([sys.executable,'-B',str(here/filename)],cwd=ROOT,env=clean,capture_output=True,text=True)
        need(p.returncode==0 and 'PASS_' in p.stdout, 'author toy controls '+filename+' '+p.stderr)
        observed[filename]={'exit':p.returncode,'stdout':p.stdout.strip()}
    for label,flags,envextra in [('O',['-O'],{}),('OO',['-OO'],{}),('env',[],{'PYTHONOPTIMIZE':'1'})]:
        p=subprocess.run([sys.executable,'-B',*flags,str(here/'launch.py')],cwd=ROOT,env=clean|envextra,capture_output=True,text=True)
        need(p.returncode!=0 and 'launcher rejects optimized' in p.stderr and not p.stdout, 'launcher guard '+label)
        observed['guard_'+label]={'exit':p.returncode,'stderr_last_line':p.stderr.strip().splitlines()[-1]}
    p=subprocess.run([sys.executable,'-B',str(here/'launch.py'),'unexpected'],cwd=ROOT,env=clean,capture_output=True,text=True)
    need(p.returncode!=0 and 'launcher takes no arguments' in p.stderr and not p.stdout, 'argument guard')
    observed['guard_unexpected_argument']={'exit':p.returncode,'stderr_last_line':p.stderr.strip().splitlines()[-1]}

    # Independently exercise receipt semantics with recomputed enclosing hashes,
    # so rejection is not merely an outer byte-pin mismatch.
    gs=importlib.util.spec_from_file_location('historical_gates_audit',here/'gates.py')
    gates=importlib.util.module_from_spec(gs);gs.loader.exec_module(gates)
    with tempfile.TemporaryDirectory(prefix='review-receipt-audit-') as tmp:
        t=Path(tmp); receipt=t/'receipt.json';terminal=t/'terminal.json'
        def h(path): return hashlib.sha256(path.read_bytes()).hexdigest()
        def write(status='PASS',exit_code=0,claimed=None):
            receipt.write_text(json.dumps({'status':status}))
            terminal.write_text(json.dumps({'observed_exit_code':exit_code,'receipt_sha256':claimed or h(receipt)}))
        def call(status='PASS',receipt_pin=None,terminal_pin=None):
            return gates.check_review(receipt,receipt_pin or h(receipt),terminal,terminal_pin or h(terminal),status,'observed_exit_code')
        def rejects(fn):
            try: fn()
            except ValueError:return
            raise ValueError('invalid review receipt accepted')
        write();need(call()['observed_exit_code']==0, 'valid review receipt')
        rejects(lambda:call(receipt_pin='0'*64));rejects(lambda:call(terminal_pin='0'*64))
        write(status='FAIL');rejects(call)
        write(exit_code=1);rejects(call)
        write(claimed='0'*64);rejects(call)
    observed['independent_receipt_controls']={'valid_accepted':True,'bad_receipt_pin_rejected':True,
        'bad_terminal_pin_rejected':True,'wrong_status_rejected':True,'nonzero_exit_rejected':True,
        'wrong_claimed_receipt_hash_rejected':True}

    # Import the exact launcher and replace preflight and all output paths with
    # a private fake fixture. Its Popen is NOT patched: a real Python child
    # runs a fake paired.py which only reports its environment and exits.
    spec=importlib.util.spec_from_file_location('historical_launcher_audit',here/'launch.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    actual_pins={}
    for path,digest in module.PINS.items():
        actual=ROOT/path.relative_to(Path(snapshot.name))
        need(hashlib.sha256(actual.read_bytes()).hexdigest()==digest, 'actual fixed pin '+str(actual))
        actual_pins[str(actual.relative_to(ROOT))]=digest
    for label,path,digest in [('source_manifest',module.SNAP/'manifest.json',module.SNAP_SHA),
                              ('provider',module.PROVIDER,module.PROVIDER_SHA),
                              ('foundation_input',module.FINPUT,module.FINPUT_SHA),
                              ('lean',module.LEAN,module.LEAN_SHA)]:
        if label == 'foundation_input': path=ROOT/path.relative_to(Path(snapshot.name))
        need(hashlib.sha256(path.read_bytes()).hexdigest()==digest, 'actual '+label+' pin')
        actual_pins[label]=digest
    observed['actual_fixed_inputs']={'sha256':actual_pins,'point_in_time_only':True}
    realpins=module.PINS
    try:
        module.PINS={Path('/no-such-audit-launch-pin'):'0'*64}
        try:module.preflight()
        except (FileNotFoundError,ValueError):pass
        else:raise ValueError('missing fixed pin accepted')
    finally:module.PINS=realpins
    observed['missing_fixed_pin']={'rejected_before_preflight':True}
    with tempfile.TemporaryDirectory(prefix='launcher-independent-audit-') as tmp:
        t=Path(tmp); fake=t/'fake-monitor'; fake.mkdir(); site=t/'pythonpath'; site.mkdir()
        (site/'sitecustomize.py').write_text("import os\nos.environ['AUDIT_SITE_EXECUTED']='yes'\n")
        (fake/'paired.py').write_text("import json,os\nkeys=['PYTHONPATH','LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT','AUDIT_SITE_EXECUTED']\nprint(json.dumps({k:os.environ.get(k) for k in keys},sort_keys=True))\n")
        module.MON=fake;module.OUTPUT=t/'pair';module.PREFLIGHT=t/'preflight.json';module.TERMINAL=t/'terminal.json'
        module.preflight=lambda:{'status':'TOY_PREFLIGHT_ONLY'}
        oldenv=os.environ.copy(); oldargv=sys.argv[:]
        try:
            os.environ.clear();os.environ.update(clean)
            os.environ.update({'PYTHONPATH':str(site),'LEAN_PATH':'AUDIT_LEAN_PATH',
                  'LEAN_SRC_PATH':'AUDIT_REMOVE','LEAN_SYSROOT':'AUDIT_REMOVE',
                  'LD_LIBRARY_PATH':'AUDIT_REMOVE','LD_PRELOAD':'AUDIT_REMOVE','LD_AUDIT':'AUDIT_REMOVE'})
            sys.argv=['launch.py']
            with contextlib.redirect_stdout(io.StringIO()),contextlib.redirect_stderr(io.StringIO()): code=module.main()
        finally:
            os.environ.clear();os.environ.update(oldenv);sys.argv=oldargv
        terminal=json.loads(module.TERMINAL.read_text());child=json.loads(terminal['stdout'])
        need(code==0 and terminal['outer_exit_code']==0, 'fake real child exit')
        need(child['PYTHONPATH']==str(site) and child['AUDIT_SITE_EXECUTED']=='yes', 'startup canary')
        need(child['LEAN_PATH']=='AUDIT_LEAN_PATH', 'inherited LEAN_PATH')
        for name in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):
            need(child[name] is None, 'scrub '+name)
        observed['real_fake_coordinator']={'outer_exit':terminal['outer_exit_code'],
             'pythonpath_inherited':True,'sitecustomize_executed':True,'lean_path_inherited':True,
             'named_scrubs_absent':True,'scope':'fake coordinator only, actual subprocess; no Lean build'}
    snapshot.cleanup()
    print(json.dumps({'status':'PASS_AUDIT_WITH_ENVIRONMENT_FINDING','reviewed_commit':'2b44686e4b',
       'pins':PINS,'observed':observed,
       'finding':'PYTHONPATH reaches the real coordinator process and sitecustomize executes at Python startup; launcher and review do not authenticate the starting Python environment. LEAN_PATH is inherited by the coordinator but fresh-project-closure/rebuild.py later sets its own LEAN_PATH.',
       'scope':'Toy controls and fake coordinator only; no build, no project or iPRA theorem, and no proof against concurrent input mutation.'},indent=2))


if __name__=='__main__':main()
